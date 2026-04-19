# E885 Forum Note Bundle

This folder contains the focused materials for the forum-facing note
[erdos885_forum_note.tex](/home/sam/lean-formalizations/FormalConjectures/Problems/Erdos/E885/ForumNote/erdos885_forum_note.tex).

It is deliberately restricted to the Lean files used in that note, so readers
do not have to sort through unrelated E885 formalizations.

## Included files

- [erdos885_forum_note.tex](/home/sam/lean-formalizations/FormalConjectures/Problems/Erdos/E885/ForumNote/erdos885_forum_note.tex)
  The LaTeX note itself.

- [erdos885_forum_note_README.md](/home/sam/lean-formalizations/FormalConjectures/Problems/Erdos/E885/ForumNote/erdos885_forum_note_README.md)
  Short companion README for the forum note.

- [Lean/AddendumComputations.lean](/home/sam/lean-formalizations/FormalConjectures/Problems/Erdos/E885/ForumNote/Lean/AddendumComputations.lean)
  Used for:
  - `new_3row_5col_packet`

- [Lean/GuidepostRigidity.lean](/home/sam/lean-formalizations/FormalConjectures/Problems/Erdos/E885/ForumNote/Lean/GuidepostRigidity.lean)
  Used for the guidepost rigidity section, including:
  - `guidepostSigma_eq`
  - `guidepostDelta_eq`
  - `guidepost_middle_value_of_common_secant`
  - `guidepostMiddleValues_eq`
  - `guidepostSquareTest_954`
  - `guidepostSquareTest_1062`
  - `guidepostSquareTest_1178`
  - `guidepostSquareTest_1402`
  - `guidepost_positive_common_factorDiffSet_iff`
  - `guidepost_seed_rigid`

- [Lean/Defs.lean](/home/sam/lean-formalizations/FormalConjectures/Problems/Erdos/E885/ForumNote/Lean/Defs.lean)
  Included because the note uses the definition of `factorDiffSet`.

- [Lean/Computations.lean](/home/sam/lean-formalizations/FormalConjectures/Problems/Erdos/E885/ForumNote/Lean/Computations.lean)
  Included because `GuidepostRigidity.lean` imports it directly.

## Notes

- This folder is a curated copy for sharing and browsing.
- It currently matches the tightened two-result forum note, not the earlier
  three-result draft.
- The canonical project files remain under
  [Findings](/home/sam/lean-formalizations/FormalConjectures/Problems/Erdos/E885/Findings).
