package slemus.hott

import fs2.io.file.Path
import scala.util.matching.Regex

final case class ChapterExercise private (
  chapter: Int,
  id: String,
  filePath: Path,
  lineNumber: Long
):
  val exerciseId = s"$chapter$id"
  def toMarkdownLine: String = s"- [Exercise $exerciseId](${filePath}#L$lineNumber)"

object ChapterExercise:
  private val chapterGroup = "ch"
  private val idGroup = "id"
  private val exerciseRegex = Regex(
    raw"""Exercise\s*(?<$chapterGroup>\d+)(?<$idGroup>(?:\.(?:\d+|\w+))*)""",
    chapterGroup,
    idGroup
  )

  def make(path: Path, line: String, lineNumber: Long): Option[ChapterExercise] =
    for
      hit <- exerciseRegex.findFirstMatchIn(line)
      chapter <- hit.group(chapterGroup).toIntOption
      id = hit.group(idGroup)
    yield ChapterExercise(chapter, id, path, lineNumber)
