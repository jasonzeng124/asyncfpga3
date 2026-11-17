module {
  func.func @triangular(%arg0: memref<10xi32>, %arg1: i32, %arg2: memref<100xi32>) {
    %c-1_i32 = arith.constant -1 : i32
    %c0_i32 = arith.constant 0 : i32
    %c-2_i32 = arith.constant -2 : i32
    %0 = arith.addi %arg1, %c-1_i32 : i32
    %1 = arith.cmpi sgt, %arg1, %c0_i32 : i32
    cf.cond_br %1, ^bb2(%0, %arg1 : i32, i32), ^bb4
  ^bb1:  // 2 preds: ^bb2, ^bb3
    %2 = arith.addi %4, %c-1_i32 : i32
    %3 = arith.cmpi sgt, %4, %c0_i32 : i32
    cf.cond_br %3, ^bb2(%2, %4 : i32, i32), ^bb4
  ^bb2(%4: i32, %5: i32):  // 2 preds: ^bb0, ^bb1
    %6 = arith.addi %5, %c-2_i32 : i32
    %7 = arith.cmpi sgt, %6, %c-1_i32 : i32
    cf.cond_br %7, ^bb3(%6 : i32), ^bb1
  ^bb3(%8: i32):  // 2 preds: ^bb2, ^bb3
    %9 = arith.extsi %8 : i32 to i64
    %10 = arith.extsi %4 : i32 to i64
    %c10_i64 = arith.constant 10 : i64
    %11 = arith.muli %9, %c10_i64 : i64
    %12 = arith.addi %11, %10 : i64
    %13 = arith.index_cast %12 : i64 to index
    %14 = memref.load %arg2[%13] {handshake.name = "load0"} : memref<100xi32>
    %15 = arith.extsi %4 : i32 to i64
    %16 = arith.index_cast %15 : i64 to index
    %17 = memref.load %arg0[%16] {handshake.name = "load1"} : memref<10xi32>
    %18 = arith.muli %14, %17 : i32
    %19 = arith.extsi %8 : i32 to i64
    %20 = arith.extsi %arg1 : i32 to i64
    %c10_i64_0 = arith.constant 10 : i64
    %21 = arith.muli %19, %c10_i64_0 : i64
    %22 = arith.addi %21, %20 : i64
    %23 = arith.index_cast %22 : i64 to index
    %24 = memref.load %arg2[%23] {handshake.name = "load2"} : memref<100xi32>
    %25 = arith.subi %24, %18 : i32
    %26 = arith.index_cast %22 : i64 to index
    memref.store %25, %arg2[%26] {handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : memref<100xi32>
    %27 = arith.addi %8, %c-1_i32 : i32
    %28 = arith.cmpi sgt, %27, %c-1_i32 : i32
    cf.cond_br %28, ^bb3(%27 : i32), ^bb1
  ^bb4:  // 2 preds: ^bb0, ^bb1
    return
  }
}
