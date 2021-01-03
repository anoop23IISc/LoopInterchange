# LoopInterchange

- Developed a loop interchange tool in MLIR to speed up matrix operations
- The tool optimizes for locality (both spatial & temporal) and parallelism for multi-cores.
- Driven by an analytical cost model, implemented on Affine dialect in MLIR.
