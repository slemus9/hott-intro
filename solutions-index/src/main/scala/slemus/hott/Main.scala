package slemus.hott

import cats.effect.{IOApp, IO}
import cats.syntax.traverse.*
import fs2.{Stream, Pipe, Pure}
import fs2.io.file.{Files, Path}

object Main extends IOApp.Simple:

  // TODO: the title, input directory and output file paths should be arguments to the program
  val title = "# Solutions Index"
  val outFileName = "SolutionsIndex.md"
  val groupNameId = "ex"
  val exerciseRegex = """Exercise\s*(?<ex>\d+(?:\.(?:\d+|\w+))*)""".r

  def run: IO[Unit] = 
    val outPath = Path("..") / outFileName
    Files[IO].deleteIfExists(outPath) >>
      Files[IO].walk(Path("../src"))
        .filter(_.extName == ".agda")
        .through(extractAllExercises(20)) // TODO: Make the chunk size an argument to the program
        .through(makeMarkdownLines)
        .through(Files[IO].writeUtf8Lines(outPath))
        .compile
        .drain

  def makeMarkdownLines(exercises: Stream[IO, Exercise]): Stream[IO, String] =
    Stream(title) ++ exercises.map(_.toMarkdownLine)

  def extractAllExercises(chunkSize: Int): Pipe[IO, Path, Exercise] = 
    _.flatMap(extractFileExercises).through(sortExerciseStream(chunkSize))

  def extractFileExercises(path: Path): Stream[IO, Exercise] = 
    Files[IO].readUtf8Lines(path)
      .zip(intsFrom(1))
      .flatMap(
        extractLineExercise(path).andThen(Stream.fromOption(_))
      )

  // We assume that there is only one "Exercise" annotation per line
  def extractLineExercise(path: Path): ((String, Int)) => Option[Exercise] = 
    (line, lineNumber) => exerciseRegex.findFirstMatchIn(line).map { m => 
      val normalizedPath = Path(".") / Path("..").relativize(path)
      Exercise(m.group(groupNameId), normalizedPath, lineNumber)  
    }

  /* 
    I don't expect that the number of exercises will exceed the memory capacity.
    If that is the case, we should re-implement this function 
  */
  def sortExerciseStream(chunkSize: Int): Pipe[IO, Exercise, Exercise] = s =>
    Stream.eval(s.compile.toList).flatMap { l => 
      Stream.fromIterator(l.sortBy(_.id).iterator, chunkSize)
    }

  def intsFrom(i: Int): Stream[Pure, Int] = Stream(i) ++ intsFrom(i + 1) 

end Main