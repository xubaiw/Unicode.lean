import Lake
open Lake DSL

package includes {
  dependencies := #[{
    name := `Unicode
    src := Source.path (".." / "..")
  }]
}
