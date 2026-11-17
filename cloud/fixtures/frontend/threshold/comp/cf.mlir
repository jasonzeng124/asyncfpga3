module {
  func.func @threshold(%arg0: i32, %arg1: memref<1000xi32>, %arg2: memref<1000xi32>, %arg3: memref<1000xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c1000_i32 = arith.constant 1000 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.index_cast %1 : i64 to index
    %3 = memref.load %arg1[%2] {handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : memref<1000xi32>
    %4 = arith.extui %0 : i32 to i64
    %5 = arith.index_cast %4 : i64 to index
    %6 = memref.load %arg2[%5] {handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load1"} : memref<1000xi32>
    %7 = arith.addi %3, %6 : i32
    %8 = arith.extui %0 : i32 to i64
    %9 = arith.index_cast %8 : i64 to index
    %10 = memref.load %arg3[%9] {handshake.deps = #handshake<deps[{dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load2"} : memref<1000xi32>
    %11 = arith.addi %7, %10 : i32
    %12 = arith.cmpi sgt, %11, %arg0 : i32
    cf.cond_br %12, ^bb3, ^bb2
  ^bb2:  // pred: ^bb1
    %13 = arith.extui %0 : i32 to i64
    %14 = arith.index_cast %13 : i64 to index
    memref.store %c0_i32, %arg1[%14] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : memref<1000xi32>
    %15 = arith.extui %0 : i32 to i64
    %16 = arith.index_cast %15 : i64 to index
    memref.store %c0_i32, %arg2[%16] {handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : memref<1000xi32>
    %17 = arith.extui %0 : i32 to i64
    %18 = arith.index_cast %17 : i64 to index
    memref.store %c0_i32, %arg3[%18] {handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : memref<1000xi32>
    cf.br ^bb3
  ^bb3:  // 2 preds: ^bb1, ^bb2
    %19 = arith.addi %0, %c1_i32 : i32
    %20 = arith.cmpi ult, %19, %c1000_i32 : i32
    cf.cond_br %20, ^bb1(%19 : i32), ^bb4
  ^bb4:  // pred: ^bb3
    return
  }
}
