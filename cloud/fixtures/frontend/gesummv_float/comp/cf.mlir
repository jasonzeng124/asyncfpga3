module {
  func.func @gesummv_float(%arg0: f32, %arg1: f32, %arg2: memref<900xf32>, %arg3: memref<900xf32>, %arg4: memref<30xf32>, %arg5: memref<30xf32>, %arg6: memref<30xf32>) {
    %c0_i32 = arith.constant 0 : i32
    %cst = arith.constant 0.000000e+00 : f32
    %c1_i32 = arith.constant 1 : i32
    %c30_i32 = arith.constant 30 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.extui %0 : i32 to i64
    cf.br ^bb2(%cst, %cst, %c0_i32 : f32, f32, i32)
  ^bb2(%3: f32, %4: f32, %5: i32):  // 2 preds: ^bb1, ^bb2
    %6 = arith.extui %5 : i32 to i64
    %c30_i64 = arith.constant 30 : i64
    %7 = arith.muli %1, %c30_i64 : i64
    %8 = arith.addi %7, %6 : i64
    %9 = arith.index_cast %8 : i64 to index
    %10 = memref.load %arg3[%9] {handshake.name = "load0"} : memref<900xf32>
    %11 = arith.extui %5 : i32 to i64
    %12 = arith.index_cast %11 : i64 to index
    %13 = memref.load %arg6[%12] {handshake.name = "load1"} : memref<30xf32>
    %14 = arith.mulf %10, %13 : f32
    %15 = arith.addf %14, %3 : f32
    %16 = arith.extui %5 : i32 to i64
    %c30_i64_0 = arith.constant 30 : i64
    %17 = arith.muli %2, %c30_i64_0 : i64
    %18 = arith.addi %17, %16 : i64
    %19 = arith.index_cast %18 : i64 to index
    %20 = memref.load %arg2[%19] {handshake.name = "load2"} : memref<900xf32>
    %21 = arith.mulf %20, %13 : f32
    %22 = arith.addf %21, %4 : f32
    %23 = arith.addi %5, %c1_i32 : i32
    %24 = arith.cmpi ult, %23, %c30_i32 : i32
    cf.cond_br %24, ^bb2(%15, %22, %23 : f32, f32, i32), ^bb3(%22, %15 : f32, f32)
  ^bb3(%25: f32, %26: f32):  // pred: ^bb2
    %27 = arith.extui %0 : i32 to i64
    %28 = arith.index_cast %27 : i64 to index
    memref.store %25, %arg4[%28] {handshake.name = "store3"} : memref<30xf32>
    %29 = arith.mulf %25, %arg0 : f32
    %30 = arith.mulf %26, %arg1 : f32
    %31 = arith.addf %29, %30 : f32
    %32 = arith.extui %0 : i32 to i64
    %33 = arith.index_cast %32 : i64 to index
    memref.store %31, %arg5[%33] {handshake.name = "store4"} : memref<30xf32>
    %34 = arith.addi %0, %c1_i32 : i32
    %35 = arith.cmpi ult, %34, %c30_i32 : i32
    cf.cond_br %35, ^bb1(%34 : i32), ^bb4
  ^bb4:  // pred: ^bb3
    return
  }
}
