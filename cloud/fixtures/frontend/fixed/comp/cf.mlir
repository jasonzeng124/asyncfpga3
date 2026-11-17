module {
  memref.global "private" constant @".str" : memref<9xi8> = dense<[115, 116, 97, 110, 100, 97, 114, 100, 0]> {alignment = 1 : i64}
  func.func @fixed(%arg0: f32) -> f32 {
    %cst = arith.constant 1.000000e+00 : f32
    %cst_0 = arith.constant 9.99999993E-9 : f32
    %c4_i32 = arith.constant 4 : i32
    %0 = memref.get_global @".str" : memref<9xi8>
    cf.br ^bb1(%cst : f32)
  ^bb1(%1: f32):  // 2 preds: ^bb0, ^bb1
    %2 = arith.mulf %1, %arg0 : f32
    %3 = arith.subf %1, %2 : f32
    %4 = arith.cmpf oge, %3, %cst_0 : f32
    %5 = "dynamatic.producer_output_attr_marker"(%4) {dynamatic.speculate = {max_predictions = 4 : i64, style = "standard"}} : (i1) -> i1
    cf.cond_br %5, ^bb1(%2 : f32), ^bb2(%2 : f32)
  ^bb2(%6: f32):  // pred: ^bb1
    return %6 : f32
  }
}
