module {
  func.func @if_loop_mul(%arg0: memref<1000xf32> {handshake.arg_name = "a"}, %arg1: memref<1000xf32> {handshake.arg_name = "b"}) -> f32 {
    %cst = arith.constant {handshake.name = "constant0"} 1.000000e+00 : f32
    %c0_i32 = arith.constant {handshake.name = "constant1"} 0 : i32
    cf.br ^bb1(%cst, %c0_i32 : f32, i32) {handshake.name = "br0"}
  ^bb1(%0: f32, %1: i32):  // 2 preds: ^bb0, ^bb1
    %c1000_i32 = arith.constant {handshake.name = "constant5"} 1000 : i32
    %c1_i32 = arith.constant {handshake.name = "constant6"} 1 : i32
    %cst_0 = arith.constant {handshake.name = "constant7"} 0.000000e+00 : f32
    %2 = arith.extui %1 {handshake.name = "extui0"} : i32 to i64
    %3 = arith.index_cast %2 {handshake.name = "index_cast0"} : i64 to index
    %4 = memref.load %arg0[%3] {handshake.name = "load0"} : memref<1000xf32>
    %5 = arith.extui %1 {handshake.name = "extui1"} : i32 to i64
    %6 = arith.index_cast %5 {handshake.name = "index_cast1"} : i64 to index
    %7 = memref.load %arg1[%6] {handshake.name = "load1"} : memref<1000xf32>
    %8 = arith.subf %4, %7 {handshake.name = "subf0"} : f32
    %9 = arith.cmpf ult, %8, %cst_0 {handshake.name = "cmpf0"} : f32
    %10 = arith.mulf %0, %8 {handshake.name = "mulf0"} : f32
    %11 = arith.select %9, %0, %10 {handshake.name = "select0"} : f32
    %12 = arith.addi %1, %c1_i32 {handshake.name = "addi0"} : i32
    %13 = arith.cmpi ult, %12, %c1000_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %13, ^bb1(%11, %12 : f32, i32), ^bb2(%11 : f32) {handshake.name = "cond_br0"}
  ^bb2(%14: f32):  // pred: ^bb1
    return {handshake.name = "return0"} %14 : f32
  }
}

