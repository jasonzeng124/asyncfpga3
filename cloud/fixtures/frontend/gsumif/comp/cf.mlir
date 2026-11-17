module {
  func.func @gsumif(%arg0: memref<1000xf32>) -> f32 {
    %c0_i32 = arith.constant 0 : i32
    %cst = arith.constant 0.000000e+00 : f32
    %c5_i32 = arith.constant 5 : i32
    %cst_0 = arith.constant 2.500000e-01 : f32
    %cst_1 = arith.constant 5.000000e-01 : f32
    %cst_2 = arith.constant 1.250000e-01 : f32
    %cst_3 = arith.constant 6.400000e-01 : f32
    %cst_4 = arith.constant 0.699999988 : f32
    %cst_5 = arith.constant 2.100000e-01 : f32
    %c1_i32 = arith.constant 1 : i32
    %c1000_i32 = arith.constant 1000 : i32
    cf.br ^bb1(%c0_i32, %cst : i32, f32)
  ^bb1(%0: i32, %1: f32):  // 2 preds: ^bb0, ^bb6
    %2 = arith.extui %0 : i32 to i64
    %3 = arith.index_cast %2 : i64 to index
    %4 = memref.load %arg0[%3] {handshake.name = "load0"} : memref<1000xf32>
    %5 = arith.cmpf ult, %4, %cst : f32
    cf.cond_br %5, ^bb6(%1 : f32), ^bb2
  ^bb2:  // pred: ^bb1
    %6 = arith.cmpi ugt, %0, %c5_i32 : i32
    cf.cond_br %6, ^bb3, ^bb4
  ^bb3:  // pred: ^bb2
    %7 = arith.addf %4, %cst_0 : f32
    %8 = arith.mulf %7, %4 : f32
    %9 = arith.addf %8, %cst_1 : f32
    %10 = arith.mulf %9, %4 : f32
    %11 = arith.addf %10, %cst_2 : f32
    cf.br ^bb5(%11 : f32)
  ^bb4:  // pred: ^bb2
    %12 = arith.addf %4, %cst_3 : f32
    %13 = arith.mulf %12, %4 : f32
    %14 = arith.addf %13, %cst_4 : f32
    %15 = arith.mulf %14, %4 : f32
    %16 = arith.addf %15, %cst_5 : f32
    cf.br ^bb5(%16 : f32)
  ^bb5(%17: f32):  // 2 preds: ^bb3, ^bb4
    %18 = arith.addf %1, %17 : f32
    cf.br ^bb6(%18 : f32)
  ^bb6(%19: f32):  // 2 preds: ^bb1, ^bb5
    %20 = arith.addi %0, %c1_i32 : i32
    %21 = arith.cmpi ult, %20, %c1000_i32 : i32
    cf.cond_br %21, ^bb1(%20, %19 : i32, f32), ^bb7(%19 : f32)
  ^bb7(%22: f32):  // pred: ^bb6
    return %22 : f32
  }
}
