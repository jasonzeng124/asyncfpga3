module {
  func.func @test_smallbound(%arg0: memref<4xi32>, %arg1: memref<2xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c2_i32 = arith.constant 2 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.extui %0 : i32 to i64
    cf.br ^bb2(%c0_i32 : i32)
  ^bb2(%3: i32):  // 2 preds: ^bb1, ^bb2
    %4 = arith.index_cast %1 : i64 to index
    %5 = memref.load %arg1[%4] {handshake.name = "load0"} : memref<2xi32>
    %c0 = arith.constant 0 : index
    %6 = memref.load %arg0[%c0] {handshake.name = "load1"} : memref<4xi32>
    %7 = arith.addi %5, %6 : i32
    %8 = arith.extui %3 : i32 to i64
    %c1_i64 = arith.constant 1 : i64
    %9 = arith.shli %2, %c1_i64 : i64
    %10 = arith.addi %9, %8 : i64
    %11 = arith.index_cast %10 : i64 to index
    memref.store %7, %arg0[%11] {handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : memref<4xi32>
    %12 = arith.addi %3, %c1_i32 : i32
    %13 = arith.cmpi ult, %12, %c2_i32 : i32
    cf.cond_br %13, ^bb2(%12 : i32), ^bb3
  ^bb3:  // pred: ^bb2
    %14 = arith.addi %0, %c1_i32 : i32
    %15 = arith.cmpi ult, %14, %c2_i32 : i32
    cf.cond_br %15, ^bb1(%14 : i32), ^bb4
  ^bb4:  // pred: ^bb3
    return
  }
}
