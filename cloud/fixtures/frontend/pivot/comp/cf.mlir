module {
  func.func @pivot(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>, %arg2: i32, %arg3: i32) {
    %c1_i32 = arith.constant 1 : i32
    %c0_i32 = arith.constant 0 : i32
    %0 = arith.addi %arg3, %c1_i32 : i32
    %1 = arith.cmpi slt, %arg3, %arg2 : i32
    cf.cond_br %1, ^bb1(%0, %c0_i32 : i32, i32), ^bb2
  ^bb1(%2: i32, %3: i32):  // 2 preds: ^bb0, ^bb1
    %4 = arith.extsi %arg3 : i32 to i64
    %5 = arith.index_cast %4 : i64 to index
    memref.store %3, %arg0[%5] {handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store0"} : memref<1000xi32>
    %6 = arith.extsi %arg3 : i32 to i64
    %7 = arith.index_cast %6 : i64 to index
    %8 = memref.load %arg0[%7] {handshake.name = "load1"} : memref<1000xi32>
    %9 = arith.extsi %2 : i32 to i64
    %10 = arith.index_cast %9 : i64 to index
    %11 = memref.load %arg1[%10] {handshake.name = "load2"} : memref<1000xi32>
    %12 = arith.extsi %2 : i32 to i64
    %13 = arith.index_cast %12 : i64 to index
    %14 = memref.load %arg0[%13] {handshake.name = "load3"} : memref<1000xi32>
    %15 = arith.muli %11, %14 : i32
    %16 = arith.subi %8, %15 : i32
    %17 = arith.addi %2, %c1_i32 : i32
    %18 = arith.cmpi slt, %2, %arg2 : i32
    cf.cond_br %18, ^bb1(%17, %16 : i32, i32), ^bb2
  ^bb2:  // 2 preds: ^bb0, ^bb1
    return
  }
}
