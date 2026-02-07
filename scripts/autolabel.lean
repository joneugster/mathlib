/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Damiano Testa
-/
import Lean.Elab.Command
import Cli.Basic

/-!
# Automatic labelling of PRs

This file contains the script to automatically assign a GitHub label to a PR.

## Label definition

The mapping from GitHub labels to Mathlib folders is done in this file and
needs to be updated here if necessary:

* `AutoLabel.mathlibLabels` contains an assignment of GitHub labels to folders inside
  the mathlib repository. If no folder is specified, a label like `t-set-theory` will be
  interpreted as matching the folder `"Mathlib" / "SetTheory"`.
* `AutoLabel.mathlibUnlabelled` contains subfolders of `Mathlib/` which are deliberately
  left without topic label.

## lake exe autolabel

`lake exe autolabel` uses `git diff --name-only origin/master...HEAD` to determine which
files have been modified and then finds all labels which should be added based on these changes.
These are printed for testing purposes.

See `lake exe autolabel --help` for all arguments available.

For the time being, the script only adds a label if it finds a **single unique label**
which would apply. If multiple labels are found, nothing happens.

## Workflow

There is a mathlib workflow `.github/workflows/add_label_from_diff.yaml` which executes
this script automatically.

Currently it is set to run only one time when a PR is created.

## Tests

Additionally, the script does a few consistency checks:

- it ensures all paths in specified in `AutoLabel.mathlibLabels` exist
- It makes sure all subfolders of `Mathlib/` belong to at least one label.
  There is `AutoLabel.mathlibUnlabelled` to add exceptions for this test.

-/

open Lean System

namespace AutoLabel

/--
A `Label` consists of the
* The `label` field is the actual GitHub label name.
* The `dirs` field is the array of all "root paths" such that a modification in a file contained
  in one of these paths should be labelled with `label`.
* The `exclusions` field is the array of all "root paths" that are excluded, among the
  ones that start with the ones in `dirs`.
  Any modifications to a file in an excluded path is ignored for the purposes of labelling.
-/
structure Label where
  /-- The label name as it appears on GitHub -/
  label : String
  /-- Array of paths which fall under this label. e.g. `"Mathlib" / "Algebra"`.

  For a label of the form `t-set-theory` this defaults to `#["Mathlib" / "SetTheory"]`. -/
  dirs : Array FilePath := if label.startsWith "t-" then
      #["Mathlib" / ("".intercalate (label.splitOn "-" |>.drop 1 |>.map .capitalize))]
    else #[]
  /-- Array of paths which should be excluded.
  Any modifications to a file in an excluded path are ignored for the purposes of labelling. -/
  exclusions : Array FilePath := #[]
  deriving BEq, Hashable

/--
Mathlib labels and their corresponding folders. Add new labels and folders here!
-/
def mathlibLabels : Array Label := #[
  { label := "t-algebra",
    dirs := #[
      "Mathlib" / "Algebra",
      "Mathlib" / "FieldTheory",
      "Mathlib" / "RepresentationTheory",
      "Mathlib" / "LinearAlgebra"] },
  { label := "t-algebraic-geometry",
    dirs := #[
      "Mathlib" / "AlgebraicGeometry",
      "Mathlib" / "Geometry" / "RingedSpace"] },
  { label := "t-algebraic-topology",
    dirs := #["Mathlib" / "AlgebraicTopology"] },
  { label := "t-analysis" },
  { label := "t-category-theory" },
  { label := "t-combinatorics" },
  { label := "t-computability" },
  { label := "t-condensed" },
  { label := "t-convex-geometry",
    dirs := #["Mathlib" / "Geometry" / "Convex"] },
  { label := "t-data"
    dirs := #[
      "Mathlib" / "Control",
      "Mathlib" / "Data",] },
  { label := "t-differential-geometry",
    dirs := #["Mathlib" / "Geometry" / "Manifold"] },
  { label := "t-dynamics" },
  { label := "t-euclidean-geometry",
    dirs := #["Mathlib" / "Geometry" / "Euclidean"] },
  { label := "t-geometric-group-theory",
    dirs := #["Mathlib" / "Geometry" / "Group"] },
  { label := "t-group-theory",
    dirs := #["Mathlib" / "GroupTheory"] },
  { label := "t-linter",
    dirs := #[
      "Mathlib" / "Tactic" / "Linter",
      "scripts" / "lint-style.lean",
      "scripts" / "lint-style.py",
    ] },
  { label := "t-logic",
    dirs := #[
      "Mathlib" / "Logic",
      "Mathlib" / "ModelTheory"] },
  { label := "t-measure-probability",
    dirs := #[
      "Mathlib" / "MeasureTheory",
      "Mathlib" / "Probability",
      "Mathlib" / "InformationTheory"] },
  { label := "t-meta",
    dirs := #[
      "Mathlib" / "Lean",
      "Mathlib" / "Mathport",
      "Mathlib" / "Tactic",
      "Mathlib" / "Util"],
    exclusions := #["Mathlib" / "Tactic" / "Linter"] },
  { label := "t-number-theory" },
  { label := "t-order" },
  { label := "t-ring-theory",
    dirs := #["Mathlib" / "RingTheory"] },
  { label := "t-set-theory" },
  { label := "t-topology",
    dirs := #["Mathlib" / "Topology"] },
  { label := "CI",
    dirs := #[
      ".github",
      "scripts",
    ],
    exclusions := #[
      "scripts" / "lint-style.lean",
      "scripts" / "lint-style.py",
      "scripts" / "noshake.json",
      "scripts" / "nolints.json",
      "scripts" / "nolints-style.txt",
      "scripts" / "nolints_prime_decls.txt",
    ] },
  { label := "IMO",
    dirs := #["Archive" / "Imo"] },
  { label := "dependency-bump",
    dirs := #["lake-manifest.json"] } ]

/-- Exceptions inside `Mathlib/` which are not covered by any label. -/
def mathlibUnlabelled : Array FilePath := #[
    "Mathlib" / "Deprecated",
    "Mathlib" / "Init",
    "Mathlib" / "Testing",
    "Mathlib" / "Std" ]

/-- Checks if the folder `path` lies inside the folder `dir`. -/
def _root_.System.FilePath.isPrefixOf (dir path : FilePath) : Bool :=
  -- use `dir / ""` to prevent partial matching of folder names
  (dir / "").normalize.toString.isPrefixOf (path / "").normalize.toString

/--
Return all names of labels in `mathlibLabels` which match
at least one of the `files`.

* `files`: array of relative paths starting from the mathlib root directory.
-/
def getMatchingLabels (files : Array FilePath) : Array String :=
  let applicable := mathlibLabels.filter fun label ↦
    -- first exclude all files the label excludes,
    -- then see if any file remains included by the label
    let notExcludedFiles := files.filter fun file ↦
      label.exclusions.all (!·.isPrefixOf file)
    label.dirs.any (fun dir ↦ notExcludedFiles.any (dir.isPrefixOf ·))
  -- return sorted list of label names
  applicable.map (·.label) |>.qsort (· < ·)

/-!
Testing the functionality of the declarations defined in this script
-/
section Tests

-- Test `FilePath.isPrefixOf`
#guard ("Mathlib" / "Algebra" : FilePath).isPrefixOf ("Mathlib" / "Algebra" / "Basic.lean")

-- Test `FilePath.isPrefixOf` does not trigger on partial prefixes
#guard ! ("Mathlib" / "Algebra" : FilePath).isPrefixOf ("Mathlib" / "AlgebraicGeometry")

#guard getMatchingLabels #[] == #[]
-- Test default value for `label.dirs` works
#guard getMatchingLabels #["Mathlib" / "SetTheory" / "ZFC"] == #["t-set-theory"]
-- Test exclusion
#guard getMatchingLabels #["Mathlib" / "Tactic"/ "Abel.lean"] == #["t-meta"]
#guard getMatchingLabels #["Mathlib" / "Tactic"/ "Linter" / "Lint.lean"] == #["t-linter"]
#guard getMatchingLabels #[
  "Mathlib" / "Tactic"/ "Linter" / "Lint.lean",
  "Mathlib" / "Tactic" / "Abel.lean" ] == #["t-linter", "t-meta"]

-- Test targeting a file instead of a directory
#guard getMatchingLabels #["lake-manifest.json"] == #["dependency-bump"]

-- Test linting of specific changes touching linting and CI.
#guard getMatchingLabels #["scripts" / "add_deprecations.sh"] == #["CI"]
#guard getMatchingLabels #["scripts" / "lint-style.lean"] == #["t-linter"]
#guard getMatchingLabels #["Mathlib" / "Tactic" / "Linter" / "TextBased.lean",
  "scripts" / "lint-style.lean", "scripts" / "lint-style.py"] == #["t-linter"]
#guard getMatchingLabels #["scripts" / "noshake.json"] == #[]

/-- Testing function to ensure the labels defined in `mathlibLabels` cover all
subfolders of `Mathlib/`. -/
partial def findUncoveredPaths (path : FilePath) (exceptions : Array FilePath := #[]) :
    IO <| Array FilePath := do
  let mut notMatched : Array FilePath := #[]
  -- all directories inside `path`
  let subDirs ← (← path.readDir).map (·.path) |>.filterM (do FilePath.isDir ·)
  for dir in subDirs do
    -- if the sub directory is not matched by a label,
    -- we go recursively into it
    if (getMatchingLabels #[dir]).size == 0 then
      notMatched := notMatched ++ (← findUncoveredPaths dir exceptions)
  -- a directory should be flagged if none of its sub-directories is matched by a label
  -- note: we assume here the base directory, i.e. "Mathlib" is never matched by a label,
  -- therefore we skip this test.
  if notMatched.size == subDirs.size then
    if exceptions.contains path then
      return #[]
    else
      return #[path]
  else
    return notMatched

end Tests

/--
Create a message which GitHub CI parses as annotation and displays at the specified file.

Note: `file` is duplicated below so that it is also visible in the plain text output.

* `type`: "error" or "warning"
* `file`: file where the annotation should be displayed
* `title`: title of the annotation
* `message`: annotation message
-/
def githubAnnotation (type file title message : String) : String :=
  s!"::{type} file={file},title={title}::{file}: {message}"

/-- Available implementations about how to communicate with Github -/
inductive GithubInteraction where
/-- no interaction with github -/
| none
/-- use `gh` -/
| gh (pr : Nat)
/-- use `curl` with an access token -/
| curl (pr : Nat) (token : String)

open IO IO.FS IO.Process Name in
def autoLabelCli (args : Cli.Parsed) : IO UInt32 := do
  let force := args.hasFlag "force"
  let tool: GithubInteraction :=
    match ((args.flag? "pr").map (·.as! Nat)), args.hasFlag "gh", args.flag? "curl" with
    | none,    _,     _             => .none
    | some _,  false, none          => .none
    | some pr, true,  _             => .gh pr
    | some pr, false, some curlFlag => .curl pr (curlFlag.as! String)

  -- test: validate that all paths in `mathlibLabels` actually exist
  let mut valid := true
  for label in mathlibLabels do
    for dir in label.dirs do
      unless ← FilePath.pathExists dir do
        -- print github annotation error
        println <| AutoLabel.githubAnnotation "error" "scripts/autolabel.lean"
          s!"Misformatted `{ ``AutoLabel.mathlibLabels }`"
          s!"directory '{dir}' does not exist but is included by label '{label.label}'. \
          Please update `{ ``AutoLabel.mathlibLabels }`!"
        valid := false
    for dir in label.exclusions do
      unless ← FilePath.pathExists dir do
        -- print github annotation error
        println <| AutoLabel.githubAnnotation "error" "scripts/autolabel.lean"
          s!"Misformatted `{ ``AutoLabel.mathlibLabels }`"
          s!"directory '{dir}' does not exist but is excluded by label '{label.label}'. \
          Please update `{ ``AutoLabel.mathlibLabels }`!"
        valid := false
  unless valid do
    return 2

  -- test: validate that the labels cover all of the `Mathlib/` folder
  let notMatchedPaths ← findUncoveredPaths "Mathlib" (exceptions := mathlibUnlabelled)
  if notMatchedPaths.size > 0 then
    -- print github annotation warning
    -- note: only emitting a warning because the workflow is only triggered on the first commit
    -- of a PR and could therefore lead to unexpected behaviour if a folder was created later.
    println <| AutoLabel.githubAnnotation "warning" "scripts/autolabel.lean"
      s!"Incomplete `{ ``AutoLabel.mathlibLabels }`"
      s!"the following paths inside `Mathlib/` are not covered \
      by any label: {notMatchedPaths} Please modify `AutoLabel.mathlibLabels` accordingly!"
    -- return 3

  -- get the modified files
  let gitDiff ← IO.Process.run {
    cmd := "git",
    args := #["diff", "--name-only", "origin/master...HEAD"] }
  let modifiedFiles : Array FilePath := (gitDiff.splitOn "\n").toArray.map (⟨·⟩)

  -- find labels covering the modified files
  let newLabels := getMatchingLabels modifiedFiles

  println s!"::notice::Applicable labels: {newLabels}"

  match newLabels with
  | #[] =>
    println s!"::warning::no labels to add"
  | #[_] =>
    match tool with
    | .gh prNr =>
      let labelsPresent ← if force then pure "" else IO.Process.run {
        cmd := "gh"
        args := #["pr", "view", s!"{prNr}", "--json", "labels", "--jq", ".labels .[] .name"]}
      let existingLabels := labelsPresent.splitToList (· == '\n')
      let autoLabels := mathlibLabels.map (·.label)
      match existingLabels.filter autoLabels.contains with
      | [] =>
        let _ ← IO.Process.run {
          cmd := "gh",
          args := #["pr", "edit", s!"{prNr}", "--add-label", ",".intercalate newLabels.toList] }
        println s!"::notice::added label: {newLabels}"
      | t_labels_already_present  =>
        println s!"::notice::did not add labels '{newLabels}', since {t_labels_already_present} \
                  were already present"
    | .curl prNr token =>
      -- TODO: implement a verion which looks at existing labels
      println args
      let _ ← IO.Process.run {
        cmd := "curl",
        args :=  #[
          "--request", "POST",
          "--header", "Accept: application/vnd.github+json",
          "--header", s!"authorization: Bearer {token}",
          "--header", "X-GitHub-Api-Version: 2022-11-28",
          "--url", s!"https://api.github.com/repos/leanprover-community/mathlib4/issues/{prNr}/labels",
          "--data", "{\"labels\":[\"" ++ s!"{"\",\"".intercalate newLabels.toList}" ++ "\"]}"
          ]}
      println s!"::notice::added label: {newLabels}"
    | .none =>
      println s!"::notice::github interaction disabled, not adding labels."
  | _ => println s!"::notice::not adding multiple labels: {newLabels}"
  return 0

end AutoLabel

/-- Setting up command line options and help text for `lake exe autolabel` -/
def autolabel : Cli.Cmd := `[Cli|
  autolabel VIA AutoLabel.autoLabelCli; ["0.1.0"]
  "
  Determine a list of applicable mathlib labels comparing current changes to `origin/master`.

  This tool is mathlib-specific and has no application in downstream projects.
  "
  FLAGS:
    "pr" : Nat;      "the mathlib PR number. Must be combined with `--gh` or `--curl`."
    "gh";            "apply label(s) using`gh`. Usage: `lake exe autolabel --pr 20156 --gh`"
    "curl" : String; "apply label(s) using `curl`. \
                      Usage: `lake exe autolabel --pr 20156 --curl <ACCESS_TOKEN>`. \
                      (currently, this implies `--force`)"
    "force";         "apply labels even if there are already labels on the PR."
]

/-- lake exe autolabel

## Exit codes:

- `0`: success
- `1`: invalid arguments provided
- `2`: invalid labels defined
- `3`: ~labels do not cover all of `Mathlib/`~ (unused; only emitting warning)
-/
public def main (args : List String) : IO UInt32 :=
  autolabel.validate args
