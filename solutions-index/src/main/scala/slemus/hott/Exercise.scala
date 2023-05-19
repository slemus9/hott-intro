package slemus.hott

import fs2.io.file.Path

final case class Exercise(id: String, filePath: Path, lineNumber: Int):
  def toMarkdownLine: String = s"- [Exercise $id](${filePath}#L$lineNumber)"
