module {
  func.func @jacobi_1d_imper(%arg0: memref<100xi32>, %arg1: memref<100xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c-1_i32 = arith.constant -1 : i32
    %c3_i32 = arith.constant 3 : i32
    %c99_i32 = arith.constant 99 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb4
    cf.br ^bb2(%c1_i32 : i32)
  ^bb2(%1: i32):  // 2 preds: ^bb1, ^bb2
    %2 = arith.addi %1, %c-1_i32 : i32
    %3 = arith.extsi %2 : i32 to i64
    %4 = arith.index_cast %3 : i64 to index
    %5 = memref.load %arg0[%4] {handshake.name = "load0"} : memref<100xi32>
    %6 = arith.extui %1 : i32 to i64
    %7 = arith.index_cast %6 : i64 to index
    %8 = memref.load %arg0[%7] {handshake.name = "load1"} : memref<100xi32>
    %9 = arith.addi %5, %8 : i32
    %10 = arith.addi %1, %c1_i32 : i32
    %11 = arith.extui %10 : i32 to i64
    %12 = arith.index_cast %11 : i64 to index
    %13 = memref.load %arg0[%12] {handshake.name = "load2"} : memref<100xi32>
    %14 = arith.addi %9, %13 : i32
    %15 = arith.muli %14, %c3_i32 : i32
    %16 = arith.extui %1 : i32 to i64
    %17 = arith.index_cast %16 : i64 to index
    memref.store %15, %arg1[%17] {handshake.deps = #handshake<deps[{dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : memref<100xi32>
    %18 = arith.addi %1, %c1_i32 : i32
    %19 = arith.cmpi ult, %18, %c99_i32 : i32
    cf.cond_br %19, ^bb2(%18 : i32), ^bb3(%c1_i32 : i32)
  ^bb3(%20: i32):  // 2 preds: ^bb2, ^bb3
    %21 = arith.extui %20 : i32 to i64
    %22 = arith.index_cast %21 : i64 to index
    %23 = memref.load %arg1[%22] {handshake.name = "load4"} : memref<100xi32>
    %24 = arith.extui %20 : i32 to i64
    %25 = arith.index_cast %24 : i64 to index
    memref.store %23, %arg0[%25] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : memref<100xi32>
    %26 = arith.addi %20, %c1_i32 : i32
    %27 = arith.cmpi ult, %26, %c99_i32 : i32
    cf.cond_br %27, ^bb3(%26 : i32), ^bb4
  ^bb4:  // pred: ^bb3
    %28 = arith.addi %0, %c1_i32 : i32
    %29 = arith.cmpi ult, %28, %c3_i32 : i32
    cf.cond_br %29, ^bb1(%28 : i32), ^bb5
  ^bb5:  // pred: ^bb4
    return
  }
}
