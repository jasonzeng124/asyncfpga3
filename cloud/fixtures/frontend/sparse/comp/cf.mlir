module {
  memref.global "private" constant @".str" : memref<4xi8> = dense<[91, 48, 93, 0]> {alignment = 1 : i64}
  memref.global "private" constant @".str.1" : memref<6xi8> = dense<[115, 116, 97, 114, 116, 0]> {alignment = 1 : i64}
  memref.global "private" constant @".str.2" : memref<6xi8> = dense<[102, 108, 111, 97, 116, 0]> {alignment = 1 : i64}
  memref.global "private" constant @".str.3" : memref<1xi8> = dense<0> {alignment = 1 : i64}
  memref.global "private" constant @".str.4" : memref<4xi8> = dense<[101, 110, 100, 0]> {alignment = 1 : i64}
  memref.global "private" constant @".str.5" : memref<9xi8> = dense<[115, 116, 97, 110, 100, 97, 114, 100, 0]> {alignment = 1 : i64}
  func.func @sparse(%arg0: memref<100xf32>, %arg1: memref<100xf32>) -> f32 {
    %cst = arith.constant 0.000000e+00 : f32
    %c0_i32 = arith.constant 0 : i32
    %c3_i32 = arith.constant 3 : i32
    %c1_i32 = arith.constant 1 : i32
    %0 = memref.get_global @".str" : memref<4xi8>
    %1 = memref.get_global @".str.1" : memref<6xi8>
    %2 = memref.get_global @".str.2" : memref<6xi8>
    %3 = memref.get_global @".str.3" : memref<1xi8>
    %4 = memref.get_global @".str.4" : memref<4xi8>
    %5 = memref.get_global @".str.3" : memref<1xi8>
    %6 = memref.get_global @".str.5" : memref<9xi8>
    cf.br ^bb1(%cst, %c0_i32 : f32, i32)
  ^bb1(%7: f32, %8: i32):  // 2 preds: ^bb0, ^bb1
    %9 = arith.extui %8 : i32 to i64
    %10 = arith.index_cast %9 : i64 to index
    %11 = memref.load %arg0[%10] {handshake.name = "load0"} : memref<100xf32>
    %12 = arith.extui %8 : i32 to i64
    %13 = arith.index_cast %12 : i64 to index
    %14 = memref.load %arg1[%13] {handshake.name = "load1"} : memref<100xf32>
    %15 = arith.mulf %11, %14 : f32
    %16 = "dynamatic.prediction_marker"(%15) {dynamatic.predict = {location = "start", marker = 0 : i32, type = "float", values = "[0]"}} : (f32) -> f32
    %17 = arith.addf %7, %16 : f32
    %18 = "dynamatic.prediction_marker"(%17) {dynamatic.predict = {location = "end", marker = 0 : i32, type = "", values = ""}} : (f32) -> f32
    %19 = arith.cmpf oge, %18, %cst : f32
    %20 = "dynamatic.producer_output_attr_marker"(%19) {dynamatic.speculate = {max_predictions = 3 : i64, style = "standard"}} : (i1) -> i1
    %21 = arith.addi %8, %c1_i32 : i32
    cf.cond_br %20, ^bb1(%18, %21 : f32, i32), ^bb2(%18 : f32)
  ^bb2(%22: f32):  // pred: ^bb1
    return %22 : f32
  }
}
