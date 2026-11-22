module {
  func.func @insertion_sort(%arg0: memref<30xi32>, %arg1: i32) {
    %c1_i32 = arith.constant 1 : i32
    %c-1_i32 = arith.constant -1 : i32
    %c0_i32 = arith.constant 0 : i32
    %0 = arith.cmpi slt, %c1_i32, %arg1 : i32
    cf.cond_br %0, ^bb1(%c1_i32 : i32), ^bb5
  ^bb1(%1: i32):  // 2 preds: ^bb0, ^bb4
    %2 = arith.extui %1 : i32 to i64
    %3 = arith.index_cast %2 : i64 to index
    %4 = memref.load %arg0[%3] {handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : memref<30xi32>
    cf.br ^bb2(%1 : i32)
  ^bb2(%5: i32):  // 2 preds: ^bb1, ^bb3
    %6 = arith.addi %5, %c-1_i32 : i32
    %7 = arith.extsi %6 : i32 to i64
    %8 = arith.index_cast %7 : i64 to index
    %9 = memref.load %arg0[%8] {handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load1"} : memref<30xi32>
    %10 = arith.cmpi sgt, %9, %4 : i32
    cf.cond_br %10, ^bb3, ^bb4(%5 : i32)
  ^bb3:  // pred: ^bb2
    %11 = arith.addi %5, %c-1_i32 : i32
    %12 = arith.extsi %11 : i32 to i64
    %13 = arith.index_cast %12 : i64 to index
    %14 = memref.load %arg0[%13] {handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load2"} : memref<30xi32>
    %15 = arith.extsi %5 : i32 to i64
    %16 = arith.index_cast %15 : i64 to index
    memref.store %14, %arg0[%16] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : memref<30xi32>
    %17 = arith.addi %5, %c-1_i32 : i32
    %18 = arith.cmpi sgt, %17, %c0_i32 : i32
    cf.cond_br %18, ^bb2(%17 : i32), ^bb4(%c0_i32 : i32)
  ^bb4(%19: i32):  // 2 preds: ^bb2, ^bb3
    %20 = arith.extsi %19 : i32 to i64
    %21 = arith.index_cast %20 : i64 to index
    memref.store %4, %arg0[%21] {handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : memref<30xi32>
    %22 = arith.addi %1, %c1_i32 : i32
    %23 = arith.cmpi slt, %22, %arg1 : i32
    cf.cond_br %23, ^bb1(%22 : i32), ^bb5
  ^bb5:  // 2 preds: ^bb0, ^bb4
    return
  }
}
