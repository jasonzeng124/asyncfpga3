module {
  func.func @while_loop_1(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c1000_i32 = arith.constant 1000 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb1
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.index_cast %1 : i64 to index
    %3 = memref.load %arg0[%2] {handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : memref<1000xi32>
    %4 = arith.extui %0 : i32 to i64
    %5 = arith.index_cast %4 : i64 to index
    %6 = memref.load %arg1[%5] {handshake.name = "load1"} : memref<1000xi32>
    %7 = arith.addi %3, %6 : i32
    %8 = arith.extui %0 : i32 to i64
    %9 = arith.index_cast %8 : i64 to index
    memref.store %7, %arg0[%9] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : memref<1000xi32>
    %10 = arith.addi %0, %c1_i32 : i32
    %11 = arith.cmpi slt, %7, %c1000_i32 : i32
    cf.cond_br %11, ^bb1(%10 : i32), ^bb2
  ^bb2:  // pred: ^bb1
    return
  }
}
