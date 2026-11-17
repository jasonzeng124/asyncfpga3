module {
  func.func @if_loop_mul(%arg0: memref<1000xf32>, %arg1: memref<1000xf32>) -> f32 {
    %cst = arith.constant 1.000000e+00 : f32
    %c0_i32 = arith.constant 0 : i32
    %cst_0 = arith.constant 0.000000e+00 : f32
    %c1_i32 = arith.constant 1 : i32
    %c1000_i32 = arith.constant 1000 : i32
    cf.br ^bb1(%cst, %c0_i32 : f32, i32)
  ^bb1(%0: f32, %1: i32):  // 2 preds: ^bb0, ^bb1
    %2 = arith.extui %1 : i32 to i64
    %3 = arith.index_cast %2 : i64 to index
    %4 = memref.load %arg0[%3] {handshake.name = "load0"} : memref<1000xf32>
    %5 = arith.extui %1 : i32 to i64
    %6 = arith.index_cast %5 : i64 to index
    %7 = memref.load %arg1[%6] {handshake.name = "load1"} : memref<1000xf32>
    %8 = arith.subf %4, %7 : f32
    %9 = arith.cmpf ult, %8, %cst_0 : f32
    %10 = arith.mulf %0, %8 : f32
    %11 = arith.select %9, %0, %10 : f32
    %12 = arith.addi %1, %c1_i32 : i32
    %13 = arith.cmpi ult, %12, %c1000_i32 : i32
    cf.cond_br %13, ^bb1(%11, %12 : f32, i32), ^bb2(%11 : f32)
  ^bb2(%14: f32):  // pred: ^bb1
    return %14 : f32
  }
}
