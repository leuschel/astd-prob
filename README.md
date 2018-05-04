# astd-prob
ASTD Interpreter for the ProB model checker

This project contains a Prolog interpreter for extended
ASTDs (Algebraic State Transition Diagrams).
The interpreter can be used stand-alone or loaded by ProB,
conforming to the XTL format (https://www3.hhu.de/stups/prob/index.php/Other_languages).

This project accompanies the paper
- Extended Algebraic State-Transition Diagrams
by
- Lionel N. Tidjon, Marc Frappier, Michael Leuschel and Amel Mammar

You can load the files ending with .P directly in ProB to run the ProB
animator or model checker on them:
- SimpleASTD.P: a very simple ASTD, without global state
- LibraryASTD.P: the library case study, with global state
- PortScanAttackASTD_v3.P: a case study from a scientific article about extended ASTDs
  (needs a data file in with an attack log)
  
All these files use the main interpreter which is in the file
- ASTD_Global_Int.pl
