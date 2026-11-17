module {
  func.func @gsum(%arg0: memref<1000xf32>) -> f32 {
    %cst = arith.constant 0.000000e+00 : f32
    %c0_i32 = arith.constant 0 : i32
    %cst_0 = arith.constant 6.400000e-01 : f32
    %cst_1 = arith.constant 0.699999988 : f32
    %cst_2 = arith.constant 2.100000e-01 : f32
    %cst_3 = arith.constant 3.300000e-01 : f32
    %c1_i32 = arith.constant 1 : i32
    %c1000_i32 = arith.constant 1000 : i32
    cf.br ^bb1(%cst, %c0_i32 : f32, i32)
  ^bb1(%0: f32, %1: i32):  // 2 preds: ^bb0, ^bb3
    %2 = arith.extui %1 : i32 to i64
    %3 = arith.index_cast %2 : i64 to index
    %4 = memref.load %arg0[%3] {handshake.name = "load0"} : memref<1000xf32>
    %5 = arith.cmpf ult, %4, %cst : f32
    cf.cond_br %5, ^bb3(%0 : f32), ^bb2
  ^bb2:  // pred: ^bb1
    %6 = arith.addf %4, %cst_0 : f32
    %7 = arith.mulf %6, %4 : f32
    %8 = arith.addf %7, %cst_1 : f32
    %9 = arith.mulf %8, %4 : f32
    %10 = arith.addf %9, %cst_2 : f32
    %11 = arith.mulf %10, %4 : f32
    %12 = arith.addf %11, %cst_3 : f32
    %13 = arith.mulf %12, %4 : f32
    %14 = arith.addf %0, %13 : f32
    cf.br ^bb3(%14 : f32)
  ^bb3(%15: f32):  // 2 preds: ^bb1, ^bb2
    %16 = arith.addi %1, %c1_i32 : i32
    %17 = arith.cmpi ult, %16, %c1000_i32 : i32
    cf.cond_br %17, ^bb1(%15, %16 : f32, i32), ^bb4(%15 : f32)
  ^bb4(%18: f32):  // pred: ^bb3
    return %18 : f32
  }
}
