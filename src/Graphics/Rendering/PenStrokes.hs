{-# LANGUAGE OverloadedStrings #-}
module Graphics.Rendering.PenStrokes where
import           Control.Monad                                       (when,void)
import           Control.Monad.Catch                                 (Exception, ExitCase (..),
                                                                      MonadMask,
                                                                      MonadThrow,
                                                                      bracket,
                                                                      finally,
                                                                      generalBracket,
                                                                      throwM)
import           Control.Monad.IO.Class
import           Control.Monad.State
import           Data.Char                                           (ord)
import qualified          Data.Array as A
import           Data.Text                                           (Text (..),unpack)
import           Data.Word                                           (Word8)
import qualified Data.Vector as V
import           Foreign.C.Types                                     (CChar (..),
                                                                      CUChar (..),CInt(..))
import           Foreign.C.String (withCString)
import           Foreign.ForeignPtr (ForeignPtr,withForeignPtr)
import Foreign.Concurrent (newForeignPtr)
import           Foreign.Marshal.Alloc                               (calloc,
                                                                      free)
import           Foreign.Ptr
import           Foreign.Storable
import Foreign.Marshal.Array
import           Graphics.Rendering.FreeType.Internal
import           Graphics.Rendering.FreeType.Internal.Bitmap
import           Graphics.Rendering.FreeType.Internal.Face
import qualified Graphics.Rendering.FreeType.Internal.Glyph          as G
import           Graphics.Rendering.FreeType.Internal.GlyphSlot

import qualified Graphics.Rendering.FreeType.Internal.BitmapGlyph    as BG
import           Graphics.Rendering.FreeType.Internal.Library
import           Graphics.Rendering.FreeType.Internal.PrimitiveTypes
import qualified Graphics.Rendering.FreeType.Internal.Vector as GV
import qualified Graphics.Rendering.FreeType.Internal.SizeMetrics as FS
import qualified Graphics.Rendering.FreeType.Internal.Size as FSS
import System.IO
import Data.Bits (testBit,shiftL,shiftR)
import Data.Either (isLeft)
import Data.Char (chr)
import Debug.Trace
import Data.List (unionBy,intersperse)
import qualified Data.Map.Strict as M
data PenstrokeState = PenstrokeState { ftPtr :: FT_Library
                                     , ftDpi :: DPI
                                     }

data PenstrokeException = FTInitException Int
                        | FTMissingFont FilePath Int
                        | FTSizeError Int
                        | FTGlyphError [Int]
                        deriving Show

instance Exception PenstrokeException

type PenstrokesT m a = StateT PenstrokeState m a

data DPI = DPI Int Int

-- | initialize freetype and run penstroke commands in the monad
withPenstrokes :: (MonadIO m, MonadThrow m, MonadMask m) => DPI -- ^ monitor dpi
  -> PenstrokesT m a -- ^ the penstrokes commands to run
  -> m a
withPenstrokes dpi pens = do
    (a,e) <- generalBracket
                (liftIO calloc)
                (\p ec -> liftIO (free p) >> pure ec)
                (\ptr -> do
                    libptr <- liftIO (
                      do err <- ft_Init_FreeType ptr
                         when (err /= 0) $ throwM (FTInitException
                                                   (fromIntegral err)
                                                  )
                         peek ptr
                      )
                    evalStateT pens PenstrokeState{ftPtr=libptr,ftDpi=dpi}
                      --`finally` liftIO (foldMap ft_Done_FreeType ptr)
                )
    case e of
        ExitCaseSuccess _ -> pure a
        ExitCaseException e -> fail $ show e
        ExitCaseAbort -> fail "generalbracket aborted in withPenStrokes"


data PenWgt = ThinestPen | ThinPen | NormalPen | BoldPen | BoldestPen
  deriving (Show,Eq)

data PenDir = LeftToRight | RightToLeft deriving (Show,Eq)

data Pensmanship = PenWeight PenWgt Pensmanship
                 | PenFont FilePath Pensmanship
                 | LetterSize Int Pensmanship
                 | PenSlant Int Pensmanship
                 | PaperWidth Int Pensmanship
                 | PenDirection PenDir Pensmanship
                 | LineSpacing Double Pensmanship
                 | Write Text deriving (Show,Eq)
                 -- color? texture? probably not

data PenState = PenState { penFont      :: FilePath
                         , penWeight    :: PenWgt
                         , letterSize   :: Int
                         , penSlant     :: Int
                         , paperWidth   :: Int
                         , penDirection :: PenDir
                         , lineSpacing  :: Double
                         , toWrite      :: Text
                         } deriving (Show,Eq)

type DoneGlyphPtr = G.FT_Glyph -> IO ()
foreign import ccall "wrapper"
  mkDoneGlyphPtr :: DoneGlyphPtr -> IO (FunPtr DoneGlyphPtr)

charToGlyph :: FT_Face -> Char -> IO (Either Int (Char,ForeignPtr G.FT_GlyphRec_))
charToGlyph fc c = do
    ferr <- ft_Load_Char fc (fromIntegral $ ord c) 2
    if ferr /= 0
        then pure $ Left $ fromIntegral ferr
        else do gptrptr <- calloc
                gslotptr <- peek (glyph fc)
                gerr <- ft_Get_Glyph gslotptr gptrptr
                if gerr /= 0
                    then do free gptrptr
                            pure $ Left $ fromIntegral gerr
                    else do gptrbefore <- peek gptrptr
                            berr <- ft_Glyph_To_Bitmap gptrptr ft_RENDER_MODE_NORMAL nullPtr (CUChar 1)
                            gptrafter <- peek gptrptr
                            if berr /= 0
                                then do ft_Done_Glyph gptrbefore
                                        free gptrptr
                                        pure $ Left $ fromIntegral berr
                                else do gfptr <- newForeignPtr gptrafter (ft_Done_Glyph gptrafter)
                                        free gptrptr
                                        pure $ Right (c,gfptr)


type PxColor = (Word8,Word8,Word8,Word8)

data PxFormat = PxFormat { readPixelFromRowStart :: Ptr CChar -> Int -> IO PxColor }

peekCChar :: Ptr Word8 -> IO Word8
peekCChar = peek

pxFormatForMode :: Int -> CChar -> PxFormat
pxFormatForMode _ (CChar 1) = PxFormat $ \buff pos ->
  do b <- peekCChar $ plusPtr buff (pos `div` 8)
     if testBit b (7 - pos `mod` 8)
       then pure (255,255,255,255)
       else pure (0,0,0,0)
     
pxFormatForMode _ (CChar 2) = PxFormat $ \buff pos ->
  do b <- peekCChar $ plusPtr buff pos
     pure (b,b,b,b)

pxFormatForMode xpx (CChar 5) = PxFormat $ \buff pos ->
  do r <- peekCChar $ plusPtr buff pos
     g <- peekCChar $ plusPtr buff (pos+xpx)
     b <- peekCChar $ plusPtr buff (pos+(xpx * 2))
     pure (r,g,b,255)

pxFormatForMode _ (CChar 6) = PxFormat $ \buff pos -> -- TODO this is wrong, it needs to go vertical
  do b <- peekCChar $ plusPtr buff (pos*4)
     g <- peekCChar $ plusPtr buff (pos*4 + 1)
     r <- peekCChar $ plusPtr buff (pos*4 + 2)
     a <- peekCChar $ plusPtr buff (pos*4 + 3)
     pure (r,g,b,a)

pxFormatForMode _ _ = PxFormat $ \_ _ -> pure (0,0,0,0)

traceShowIdLabel s x = Debug.Trace.trace (s ++ ": " ++ show x) x

-- | blit a bitmap into a matrix at a given position
-- 
blitToList :: FT_Bitmap -- ^ the freetype bitmap to blit
  -> (Int,Int) -- ^ the x y position of the top left of the bitmap to blit
  -> IO [((Int,Int),PxColor)]

blitToList bm (topX,topY) =
  foldM (\as (i,j,rowptr) -> do --setColor mx' (i+topX,j+topY)
            c <- readPixelFromRowStart pxFormat rowptr i
            pure $ ((i+topX,j+topY),c): as
        ) [] (reverse bmpXYRowPtr)
  where buff = buffer bm
        (maxCols,maxRows) = pxBox (pixel_mode bm)
        bmpCols = [0..maxCols-1]
        bmpRows = [0..maxRows-1] 
        bmpRowPtr = map (plusPtr buff . fromIntegral . (*) (pitch bm)) bmpRows
        bmpXYRowPtr = [(fromIntegral x,fromIntegral y,rowPtr)
                      | x <- bmpCols, (y,rowPtr) <- zip bmpRows bmpRowPtr]
        pxFormat = pxFormatForMode (fromIntegral maxCols) (pixel_mode bm)

        pxBox (CChar 5) = (width bm `div` 3, rows bm)
        pxBox (CChar 6) = (width bm, rows bm `div` 3)
        pxBox _ = (width bm, rows bm)
        
        

writeBMPTest :: FT_Bitmap -> IO ()
writeBMPTest bmp = do
  let nb = fromIntegral (pitch bmp) * fromIntegral (rows bmp)
  withBinaryFile "/home/mdurr/test.bmp" WriteMode (\h -> hPutBuf h (buffer bmp) nb)  
  

-- | given glyphs and their positions, create a matrix that represents
-- the RGBA values that represent the glyphs
render :: (MonadIO m, MonadThrow m, MonadMask m)
  => ([(CInt,CInt,ForeignPtr G.FT_GlyphRec_)]) -- ^ the baselines and glyphs
  -> PenstrokesT m (A.Array (Int,Int) PxColor)
render gs = do
  ls <- liftIO $ foldM (\as (i,j,g) -> do
                           (bm,left,top) <- withForeignPtr g bmparams
                           pxs <- blitToList bm (fromIntegral $ i+left,fromIntegral $ j-top)
                           pure (pxs ++ as)
                       ) [] gs
  let mp = M.fromList ls
      idxs = [(x,y) | x <- [0..mx], y <- [0..my]]
      (mx,my) = foldl (\(x,y) ((i,j),_) -> (max x i, max y j)) (0,0) ls 
      fillEmpty = map (\pos -> (pos,M.findWithDefault (0,0,0,0) pos mp)) idxs
  -- fill out empty cells
  return $ A.array ((0,0),(mx,my)) fillEmpty
  where bmparams g = do
          let bmg = BG.cast g 
          bm <- peek (BG.bitmap bmg)
          i <- peek (BG.left bmg)
          j <- peek (BG.top bmg)
          pure (bm,i,j)
        


-- linespace = ascent - descent + linegap
-- line size = ascent - descent
lineSpace :: FS.FT_Size_Metrics -> Int
lineSpace met = fromIntegral
  $ shiftR (FS.height met) 6
  {- + shiftR (FS.ascender met) 6
     - shiftR (FS.descender met) 6
  -}
baseline :: FS.FT_Size_Metrics -> CInt
baseline met  = fromIntegral $ shiftR (FS.ascender met) 6


position :: (MonadIO m, MonadThrow m, MonadMask m) => PenState
  -> FS.FT_Size_Metrics -> (CInt,CInt) -> [(Char,ForeignPtr G.FT_GlyphRec_)]
  -> PenstrokesT m [(CInt,CInt,ForeignPtr G.FT_GlyphRec_)]
position _ _ (penX,penY) [] = pure []
position ps mets (penX,penY) cs@((ch,gl):gls)
  | ch == '\n' = position ps mets (penX,penY + fromIntegral (lineSpace mets)) gls
  | ch == ' ' = do
      gptr <- liftIO $ withForeignPtr gl (pure . G.advance)
      adv <- liftIO $ GV.x <$> peek gptr
      position ps mets (penX + fromIntegral (shiftR adv 16), penY) gls
  | otherwise =
    if null ws
        then pure []
        else do
            advs <- liftIO $ mapM (\gptr -> withForeignPtr gptr (pure . G.advance)) gs
            xlens <- liftIO $ mapM (\adv -> fromIntegral . flip shiftR 16 . GV.x <$> peek adv) advs
            ylen' <- liftIO $ mapM (\adv -> fromIntegral . flip shiftR 16 . GV.y <$> peek adv) advs
            let sumxlen = sum xlens
                ylen = fromIntegral $ max (lineSpace mets) $ maximum ylen'
            posH sumxlen xlens ylen

    where ws = words (map fst cs)
          gs = if null ws then [] else map snd (take (length (head ws)) cs)
          fit sxlen xlens = do
            gs' <- position ps mets (penX + sxlen,penY) (drop (length gs) cs)
            return $ (snd $ foldr (\(xl,g) (currx,gs'') -> (currx-xl,(currx-xl,penY+baseline mets,g):gs'')) (penX+sxlen,[]) (zip xlens gs)) ++ gs'
        
          posH sxlen xlens ylen
            | sxlen <= fromIntegral (paperWidth ps) - penX = fit sxlen xlens
            | sxlen <= fromIntegral (paperWidth ps) = position ps mets (0,penY + ylen) cs
            | otherwise = fit sxlen xlens

totalDimensions :: [(CInt,CInt,ForeignPtr G.FT_GlyphRec_)] -> FS.FT_Size_Metrics -> IO (CInt,CInt)
totalDimensions [] _ = pure (1,1)
totalDimensions ((posX,posBaselineY,g):gs) ms =
  do (rx,ry) <- totalDimensions gs ms
     nx <- flip shiftR 16 <$> withForeignPtr g (\gptr -> peek (G.advance gptr) >>= \v -> pure $ fromIntegral (GV.x v))
     pure (max rx (posX + nx), max ry (posBaselineY - fromIntegral (shiftR (FS.descender ms) 6))) 
 
            

writeInternal :: (MonadIO m, MonadThrow m, MonadMask m) => Pensmanship -> PenState -> PenstrokesT m (A.Array (Int,Int) PxColor)
writeInternal (PenFont f ps) st = writeInternal ps st{penFont=f}
writeInternal (PenWeight w ps) st = writeInternal ps st{penWeight=w}
writeInternal (LetterSize s ps) st = writeInternal ps st{letterSize=s}
writeInternal (PenSlant a ps) st = writeInternal ps st{penSlant=a}
writeInternal (PaperWidth px ps) st = writeInternal ps st{paperWidth=px}
writeInternal (PenDirection d ps) st = writeInternal ps st{penDirection=d}
writeInternal (LineSpacing l ps) st = writeInternal ps st{lineSpacing=l}
writeInternal (Write t) st = do
    lib <- gets ftPtr
    DPI dx dy <- gets ftDpi
    gys <- bracket
        (liftIO calloc)
        (liftIO . free)
        (\fc -> liftIO $ do
            ferr <- withCString (penFont st) (\s -> ft_New_Face lib s 0 fc)
            bracket
              (peek fc)
              (ft_Done_Face)
              (\face -> do
                  when (ferr /= 0) $ throwM $ FTMissingFont (penFont st) (fromIntegral ferr)
                  serr <- ft_Set_Char_Size face 0 (fromIntegral $ letterSize st * 64) (fromIntegral dx) (fromIntegral dy)
                  when (serr /= 0) $ throwM $ FTSizeError $ fromIntegral serr
                  glyphs <- mapM (charToGlyph face) (unpack t)
                  when (any isLeft glyphs) (throwM $ FTGlyphError [ge | Left ge <- glyphs])
                  szs <- peek (size face)
                  mets <- peek (FSS.metrics szs)
                  pure (mets,[g | Right g <- glyphs])
              )
        )
    gys' <- position st (fst gys) (0,0) (snd gys)
    mx <- render gys'
    pure mx

    

        
write :: (MonadIO m, MonadThrow m, MonadMask m) => Pensmanship -> PenstrokesT m (A.Array (Int,Int) PxColor)
write ps = writeInternal ps PenState{penFont="./Roboto.ttf",penWeight=NormalPen,letterSize=12,paperWidth=640,lineSpacing=1.0,penSlant=0,penDirection=LeftToRight,toWrite="hello world"}

test :: IO ()
test = withPenstrokes (DPI 120 120) $ do
    mx <- write (PenFont "/usr/share/fonts/google-droid/DroidSans.ttf" $ PenWeight NormalPen $ LetterSize 12 $ PaperWidth 600 $ LineSpacing 2.0 $ Write "Hello world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the paper.llo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pallo world! The sky is blue and brown and green and red and I am going to keep on typing until I run into something that looks like the edge of the pa")
    liftIO $ renderPPM "/home/mdurr/test.ppm" mx
    
mapMRows :: Monad m => A.Array (Int,Int) a -> ([a] -> m [b]) -> m (A.Array (Int,Int) b)
mapMRows ar f = do
  ls <- concat <$> sequence [getRow (fst . snd $ A.bounds ar) y | y <- [0..(snd . snd $ A.bounds ar)-1]]
  pure $ A.array (A.bounds ar) ls
  where getRow lstX y = do
          let idx = [0..(lstX - 1)]
          ls <- f $ map (\x -> ar A.! (x,y)) idx
          pure $ zip (map (\x -> (x,y)) idx) ls
          
        
   

renderPPM :: FilePath -> A.Array (Int,Int) PxColor -> IO ()
renderPPM f ar = withBinaryFile f WriteMode (void . writePPM)
  where writePPM h = do
          hPutStrLn h "P3"
          hPutStrLn h (show $ fst $ snd $ A.bounds ar)
          hPutStrLn h (show $ snd $ snd $ A.bounds ar)
          hPutStrLn h "256"
          mapMRows ar (\r -> (printRow h r) >> pure r)
        printColor (r,g,b,a) = (show $ fromIntegral r) ++ " "
          ++ (show $ fromIntegral g)
          ++ " "
          ++ (show $ fromIntegral b)
        printRow :: Handle -> [(Word8,Word8,Word8,Word8)] -> IO ()
        printRow h [] = hPutChar h '\n'
        printRow h cs = hPutStr h (unwords (map printColor cs)) >> hPutChar h '\n'

        
