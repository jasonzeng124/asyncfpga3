module {
  memref.global "private" constant @".str" : memref<4xi8> = dense<[91, 48, 93, 0]> {alignment = 1 : i64, handshake.name = "global0"}
  memref.global "private" constant @".str.1" : memref<6xi8> = dense<[115, 116, 97, 114, 116, 0]> {alignment = 1 : i64, handshake.name = "global1"}
  memref.global "private" constant @".str.2" : memref<6xi8> = dense<[102, 108, 111, 97, 116, 0]> {alignment = 1 : i64, handshake.name = "global2"}
  memref.global "private" constant @".str.3" : memref<1xi8> = dense<0> {alignment = 1 : i64, handshake.name = "global3"}
  memref.global "private" constant @".str.4" : memref<4xi8> = dense<[101, 110, 100, 0]> {alignment = 1 : i64, handshake.name = "global4"}
  memref.global "private" constant @".str.5" : memref<9xi8> = dense<[115, 116, 97, 110, 100, 97, 114, 100, 0]> {alignment = 1 : i64, handshake.name = "global5"}
  func.func @sparse(%arg0: memref<100xf32> {handshake.arg_name = "a"}, %arg1: memref<100xf32> {handshake.arg_name = "x"}) -> f32 {
    %cst = arith.constant {handshake.name = "constant0"} 0.000000e+00 : f32
    %c0_i32 = arith.constant {handshake.name = "constant1"} 0 : i32
    cf.br ^bb1(%cst, %c0_i32 : f32, i32) {handshake.name = "br0"}
  ^bb1(%0: f32, %1: i32):  // 2 preds: ^bb0, ^bb1
    %c1_i32 = arith.constant {handshake.name = "constant2"} 1 : i32
    %cst_0 = arith.constant {handshake.name = "constant4"} 0.000000e+00 : f32
    %2 = arith.extui %1 {handshake.name = "extui0"} : i32 to i64
    %3 = arith.index_cast %2 {handshake.name = "index_cast0"} : i64 to index
    %4 = memref.load %arg0[%3] {handshake.name = "load0"} : memref<100xf32>
    %5 = arith.extui %1 {handshake.name = "extui1"} : i32 to i64
    %6 = arith.index_cast %5 {handshake.name = "index_cast1"} : i64 to index
    %7 = memref.load %arg1[%6] {handshake.name = "load1"} : memref<100xf32>
    %8 = arith.mulf %4, %7 {dynamatic.predict = {location = "start", marker = 0 : i32, type = "float", values = "[0]"}, dynamatic.predict.result_idx = 0 : i32, handshake.name = "mulf0"} : f32
    %9 = arith.addf %0, %8 {dynamatic.predict = {location = "end", marker = 0 : i32, type = "", values = ""}, dynamatic.predict.result_idx = 0 : i32, handshake.name = "addf0"} : f32
    %10 = arith.cmpf oge, %9, %cst_0 {dynamatic.speculate = {max_predictions = 3 : i64, style = "standard"}, dynamatic.speculate.result_idx = 0 : i32, handshake.name = "cmpf0"} : f32
    %11 = arith.addi %1, %c1_i32 {handshake.name = "addi0"} : i32
    cf.cond_br %10, ^bb1(%9, %11 : f32, i32), ^bb2(%9 : f32) {handshake.name = "cond_br0"}
  ^bb2(%12: f32):  // pred: ^bb1
    return {handshake.name = "return0"} %12 : f32
  }
}

