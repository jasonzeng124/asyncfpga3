module {
  func.func @spmv(%arg0: i32, %arg1: memref<11xi32>, %arg2: memref<10xi32>, %arg3: memref<10xi32>, %arg4: memref<10xi32>, %arg5: memref<10xi32>) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %0 = arith.cmpi slt, %c0_i32, %arg0 : i32
    cf.cond_br %0, ^bb1(%c0_i32 : i32), ^bb4(%c0_i32 : i32)
  ^bb1(%1: i32):  // 2 preds: ^bb0, ^bb3
    %2 = arith.extui %1 : i32 to i64
    %3 = arith.index_cast %2 : i64 to index
    %4 = memref.load %arg1[%3] {handshake.name = "load0"} : memref<11xi32>
    %5 = arith.addi %1, %c1_i32 : i32
    %6 = arith.extui %5 : i32 to i64
    %7 = arith.index_cast %6 : i64 to index
    %8 = memref.load %arg1[%7] {handshake.name = "load1"} : memref<11xi32>
    %9 = arith.cmpi slt, %4, %8 : i32
    cf.cond_br %9, ^bb2(%4, %c0_i32 : i32, i32), ^bb3(%c0_i32 : i32)
  ^bb2(%10: i32, %11: i32):  // 2 preds: ^bb1, ^bb2
    %12 = arith.extsi %10 : i32 to i64
    %13 = arith.index_cast %12 : i64 to index
    %14 = memref.load %arg3[%13] {handshake.name = "load2"} : memref<10xi32>
    %15 = arith.extsi %10 : i32 to i64
    %16 = arith.index_cast %15 : i64 to index
    %17 = memref.load %arg2[%16] {handshake.name = "load3"} : memref<10xi32>
    %18 = arith.extsi %17 : i32 to i64
    %19 = arith.index_cast %18 : i64 to index
    %20 = memref.load %arg4[%19] {handshake.name = "load4"} : memref<10xi32>
    %21 = arith.muli %14, %20 : i32
    %22 = arith.addi %11, %21 : i32
    %23 = arith.addi %10, %c1_i32 : i32
    %24 = arith.cmpi ne, %23, %8 : i32
    cf.cond_br %24, ^bb2(%23, %22 : i32, i32), ^bb3(%22 : i32)
  ^bb3(%25: i32):  // 2 preds: ^bb1, ^bb2
    %26 = arith.extui %1 : i32 to i64
    %27 = arith.index_cast %26 : i64 to index
    memref.store %25, %arg5[%27] {handshake.name = "store5"} : memref<10xi32>
    %28 = arith.addi %1, %c1_i32 : i32
    %29 = arith.cmpi ne, %28, %arg0 : i32
    cf.cond_br %29, ^bb1(%28 : i32), ^bb4(%4 : i32)
  ^bb4(%30: i32):  // 2 preds: ^bb0, ^bb3
    return %30 : i32
  }
}
