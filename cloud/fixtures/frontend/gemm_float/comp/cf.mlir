module {
  func.func @gemm_float(%arg0: f32, %arg1: f32, %arg2: memref<900xf32>, %arg3: memref<900xf32>, %arg4: memref<900xf32>) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c20_i32 = arith.constant 20 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb5
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.extui %0 : i32 to i64
    %3 = arith.extui %0 : i32 to i64
    cf.br ^bb2(%c0_i32 : i32)
  ^bb2(%4: i32):  // 2 preds: ^bb1, ^bb4
    %5 = arith.extui %4 : i32 to i64
    %c30_i64 = arith.constant 30 : i64
    %6 = arith.muli %1, %c30_i64 : i64
    %7 = arith.addi %6, %5 : i64
    %8 = arith.index_cast %7 : i64 to index
    %9 = memref.load %arg4[%8] {handshake.name = "load0"} : memref<900xf32>
    %10 = arith.mulf %9, %arg1 : f32
    %11 = arith.extui %4 : i32 to i64
    cf.br ^bb3(%10, %c0_i32 : f32, i32)
  ^bb3(%12: f32, %13: i32):  // 2 preds: ^bb2, ^bb3
    %14 = arith.extui %13 : i32 to i64
    %c30_i64_0 = arith.constant 30 : i64
    %15 = arith.muli %2, %c30_i64_0 : i64
    %16 = arith.addi %15, %14 : i64
    %17 = arith.index_cast %16 : i64 to index
    %18 = memref.load %arg2[%17] {handshake.name = "load1"} : memref<900xf32>
    %19 = arith.mulf %18, %arg0 : f32
    %20 = arith.extui %13 : i32 to i64
    %c30_i64_1 = arith.constant 30 : i64
    %21 = arith.muli %20, %c30_i64_1 : i64
    %22 = arith.addi %21, %11 : i64
    %23 = arith.index_cast %22 : i64 to index
    %24 = memref.load %arg3[%23] {handshake.name = "load2"} : memref<900xf32>
    %25 = arith.mulf %19, %24 : f32
    %26 = arith.addf %12, %25 : f32
    %27 = arith.addi %13, %c1_i32 : i32
    %28 = arith.cmpi ult, %27, %c20_i32 : i32
    cf.cond_br %28, ^bb3(%26, %27 : f32, i32), ^bb4(%26 : f32)
  ^bb4(%29: f32):  // pred: ^bb3
    %30 = arith.extui %4 : i32 to i64
    %c30_i64_2 = arith.constant 30 : i64
    %31 = arith.muli %3, %c30_i64_2 : i64
    %32 = arith.addi %31, %30 : i64
    %33 = arith.index_cast %32 : i64 to index
    memref.store %29, %arg4[%33] {handshake.name = "store3"} : memref<900xf32>
    %34 = arith.addi %4, %c1_i32 : i32
    %35 = arith.cmpi ult, %34, %c20_i32 : i32
    cf.cond_br %35, ^bb2(%34 : i32), ^bb5
  ^bb5:  // pred: ^bb4
    %36 = arith.addi %0, %c1_i32 : i32
    %37 = arith.cmpi ult, %36, %c20_i32 : i32
    cf.cond_br %37, ^bb1(%36 : i32), ^bb6
  ^bb6:  // pred: ^bb5
    return
  }
}
