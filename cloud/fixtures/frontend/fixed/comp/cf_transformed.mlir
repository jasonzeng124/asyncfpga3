module {
  memref.global "private" constant @".str" : memref<9xi8> = dense<[115, 116, 97, 110, 100, 97, 114, 100, 0]> {alignment = 1 : i64, handshake.name = "global0"}
  func.func @fixed(%arg0: f32 {handshake.arg_name = "y"}) -> f32 {
    %cst = arith.constant {handshake.name = "constant0"} 1.000000e+00 : f32
    cf.br ^bb1(%cst : f32) {handshake.name = "br0"}
  ^bb1(%0: f32):  // 2 preds: ^bb0, ^bb1
    %cst_0 = arith.constant {handshake.name = "constant2"} 9.99999993E-9 : f32
    %1 = arith.mulf %0, %arg0 {handshake.name = "mulf0"} : f32
    %2 = arith.subf %0, %1 {handshake.name = "subf0"} : f32
    %3 = arith.cmpf oge, %2, %cst_0 {handshake.name = "cmpf0"} : f32
    %4 = "dynamatic.producer_output_attr_marker"(%3) {dynamatic.speculate = {max_predictions = 4 : i64, style = "standard"}, handshake.name = "producer_output_attr_marker0"} : (i1) -> i1
    cf.cond_br %4, ^bb1(%1 : f32), ^bb2(%1 : f32) {handshake.name = "cond_br0"}
  ^bb2(%5: f32):  // pred: ^bb1
    return {handshake.name = "return0"} %5 : f32
  }
}

