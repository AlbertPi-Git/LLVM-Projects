# LLVM Projects

## Introduction
These LLVM projects are part of Advanced Compiler course. There are four parts (projects) in total, from very simple static, dynamic instructions counting to reaching definition analysis, and ...

## Directory Hierarchy
All pass source codes of each part ar in the 'Passes' directory. 'Part1,2,3,4' are subdirectories of each part.

## Part 1
Part1 has three sections:
1.  counting number of static instructions in functions.
2.  counting number of dynamic instructions in functions.
3.  obtain the runtime branch bias information in functions.

## Part 2
Part2 has two sections:
1.  implement the worklist algorithm in the generic dataflow analysis class using lattice.
2.  implement the subclasses of Info class and DataFlowAnalysis class that are used for reaching definition analysis.

## Part 3
Part3 has three sections:
1.  implement the backward edge map initialization in the dataflow analysis framework.
2.  implement the subclass of Info class and DataFlowAnalysis class that are used for variable liveness analysis.
2.  implement the subclasses of Info class and DataFlowAnalysis class that are used for may point to analysis.

## Part 4
Part4 has two sections:
1.  implement a subclass of CallGraphSCC class which includes a simple version of may-point-to analysis and a must modified analysis for global variables.
2.  implement the subclass of Info class and DataFlowAnalysis class that is used for constant propagation of global variables.
