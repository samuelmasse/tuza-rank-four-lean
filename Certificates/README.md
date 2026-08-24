# Certificate artifacts

The committed reference case uses:

- `cnf/order10-skeleton06.cnf`, the frozen DIMACS instance;
- `cubes/order10-skeleton06-adaptive/manifest.json`, an exhaustive split-tree
  manifest with SHA-256 hashes; and
- the binary LRAT leaf files named by that manifest.

The binary format is the standard LRAT encoding read by Lean's own parser.
Text LRAT and intermediate DRAT files are reproducible producer artifacts and
are not part of the trusted proof object.

The manifest records both the path assignment at every leaf and every internal
split.  `scripts/materialize_adaptive_cube.py` validates that this is a rooted,
exhaustive binary tree before generating the corresponding Lean modules.
