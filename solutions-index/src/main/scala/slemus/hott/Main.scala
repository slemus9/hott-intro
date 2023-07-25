package slemus.hott

import cats.effect.{IOApp, IO}
import cats.syntax.traverse.*
import fs2.{Chunk, Stream, Pipe, Pure}
import fs2.io.file.{Files, Path}

object Main extends IOApp.Simple:

  // TODO: all these variables should be given as an input to the program
  val title = "# Solutions Index"
  val outFileName = "SolutionsIndex.md"
  val chunkSize = 20

  def run: IO[Unit] =
    val outPath = Path("..") / outFileName
    Files[IO].deleteIfExists(outPath) >>
      Files[IO].walk(Path("../src"))
        .filter(_.extName == ".agda")
        .through(extractAllExercises(chunkSize))
        .through(makeMarkdownLines)
        .through(Files[IO].writeUtf8Lines(outPath))
        .compile
        .drain

  def makeMarkdownLines(exercises: Stream[IO, ChapterExercise]): Stream[IO, String] =
    Stream(title) ++ exercises.groupAdjacentBy(_.chapter).flatMap(makeChapterMarkdown)

  def makeChapterMarkdown(chapter: Int, exercises: Chunk[ChapterExercise]): Stream[Pure, String] =
    Stream(s"## Chapter $chapter:") ++ Stream.chunk(exercises).map(_.toMarkdownLine)

  def extractAllExercises(chunkSize: Int): Pipe[IO, Path, ChapterExercise] =
    _.flatMap(extractFileExercises).through(sortExerciseStream(chunkSize))

  def extractFileExercises(path: Path): Stream[IO, ChapterExercise] =
    val normalizedPath = Path(".") / Path("..").relativize(path)
    Files[IO].readUtf8Lines(path)
      .zipWithIndex
      .flatMap { case (line, lineNumber) =>
        Stream.fromOption(ChapterExercise.make(normalizedPath, line, lineNumber + 1))
      }

  /*
    I don't expect that the number of exercises will exceed the memory capacity.
    If that is the case, we should re-implement this function
  */
  def sortExerciseStream(chunkSize: Int): Pipe[IO, ChapterExercise, ChapterExercise] = s =>
    Stream.eval(s.compile.toList).flatMap { l =>
      Stream.iterable(l.sortBy(_.exerciseId))
    }
end Main
