module {
  func.func @matrix_power(%arg0: memref<400xi32>, %arg1: memref<20xi32>, %arg2: memref<20xi32>, %arg3: memref<20xi32>) {
    %c1_i32 = arith.constant 1 : i32
    %c-1_i32 = arith.constant -1 : i32
    %c0_i32 = arith.constant 0 : i32
    %c20_i32 = arith.constant 20 : i32
    cf.br ^bb1(%c1_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %1 = arith.addi %0, %c-1_i32 : i32
    %2 = arith.extui %1 : i32 to i64
    %3 = arith.extui %0 : i32 to i64
    cf.br ^bb2(%c0_i32 : i32)
  ^bb2(%4: i32):  // 2 preds: ^bb1, ^bb2
    %5 = arith.extui %4 : i32 to i64
    %6 = arith.index_cast %5 : i64 to index
    %7 = memref.load %arg3[%6] {handshake.name = "load0"} : memref<20xi32>
    %8 = arith.extui %4 : i32 to i64
    %9 = arith.index_cast %8 : i64 to index
    %10 = memref.load %arg2[%9] {handshake.name = "load1"} : memref<20xi32>
    %11 = arith.extsi %10 : i32 to i64
    %c20_i64 = arith.constant 20 : i64
    %12 = arith.muli %2, %c20_i64 : i64
    %13 = arith.addi %12, %11 : i64
    %14 = arith.index_cast %13 : i64 to index
    %15 = memref.load %arg0[%14] {handshake.deps = #handshake<deps[{dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load2"} : memref<400xi32>
    %16 = arith.muli %7, %15 : i32
    %17 = arith.extui %4 : i32 to i64
    %18 = arith.index_cast %17 : i64 to index
    %19 = memref.load %arg1[%18] {handshake.name = "load3"} : memref<20xi32>
    %20 = arith.extsi %19 : i32 to i64
    %c20_i64_0 = arith.constant 20 : i64
    %21 = arith.muli %3, %c20_i64_0 : i64
    %22 = arith.addi %21, %20 : i64
    %23 = arith.index_cast %22 : i64 to index
    %24 = memref.load %arg0[%23] {handshake.deps = #handshake<deps[{dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load4"} : memref<400xi32>
    %25 = arith.addi %24, %16 : i32
    %26 = arith.index_cast %22 : i64 to index
    memref.store %25, %arg0[%26] {handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : memref<400xi32>
    %27 = arith.addi %4, %c1_i32 : i32
    %28 = arith.cmpi ult, %27, %c20_i32 : i32
    cf.cond_br %28, ^bb2(%27 : i32), ^bb3
  ^bb3:  // pred: ^bb2
    %29 = arith.addi %0, %c1_i32 : i32
    %30 = arith.cmpi ult, %29, %c20_i32 : i32
    cf.cond_br %30, ^bb1(%29 : i32), ^bb4
  ^bb4:  // pred: ^bb3
    return
  }
}
