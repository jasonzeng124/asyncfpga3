module {
  func.func @cordic(%arg0: f32, %arg1: memref<2xf32>, %arg2: memref<1000xf32>, %arg3: f32, %arg4: f32) -> f32 {
    %c0_i32 = arith.constant 0 : i32
    %cst = arith.constant 1.000000e+00 : f32
    %cst_0 = arith.constant 5.000000e-01 : f32
    %cst_1 = arith.constant 0.000000e+00 : f32
    %cst_2 = arith.constant -1.000000e+00 : f32
    %c1_i32 = arith.constant 1 : i32
    %c1000_i32 = arith.constant 1000 : i32
    %c1_i64 = arith.constant 1 : i64
    cf.br ^bb1(%arg0, %c0_i32, %cst, %arg3, %arg4 : f32, i32, f32, f32, f32)
  ^bb1(%0: f32, %1: i32, %2: f32, %3: f32, %4: f32):  // 2 preds: ^bb0, ^bb1
    %5 = arith.mulf %2, %cst_0 : f32
    %6 = arith.cmpf olt, %0, %cst_1 : f32
    %7 = arith.select %6, %cst_2, %cst : f32
    %8 = arith.extui %1 : i32 to i64
    %9 = arith.index_cast %8 : i64 to index
    %10 = memref.load %arg2[%9] {handshake.name = "load0"} : memref<1000xf32>
    %11 = arith.mulf %7, %10 : f32
    %12 = arith.subf %0, %11 : f32
    %13 = arith.mulf %3, %7 : f32
    %14 = arith.mulf %13, %2 : f32
    %15 = arith.addf %14, %4 : f32
    %16 = arith.mulf %4, %7 : f32
    %17 = arith.mulf %16, %2 : f32
    %18 = arith.subf %3, %17 : f32
    %19 = arith.addi %1, %c1_i32 : i32
    %20 = arith.cmpi ult, %19, %c1000_i32 : i32
    cf.cond_br %20, ^bb1(%12, %19, %5, %18, %15 : f32, i32, f32, f32, f32), ^bb2(%15, %18, %12 : f32, f32, f32)
  ^bb2(%21: f32, %22: f32, %23: f32):  // pred: ^bb1
    %c0 = arith.constant 0 : index
    memref.store %22, %arg1[%c0] {handshake.name = "store1"} : memref<2xf32>
    %c1_i64_3 = arith.constant 1 : i64
    %24 = arith.index_cast %c1_i64_3 : i64 to index
    memref.store %21, %arg1[%24] {handshake.name = "store2"} : memref<2xf32>
    return %23 : f32
  }
}
