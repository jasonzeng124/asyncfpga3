module {
  func.func @gsum(%arg0: memref<1000xf32> {handshake.arg_name = "a"}) -> f32 {
    %cst = arith.constant {handshake.name = "constant0"} 0.000000e+00 : f32
    %c0_i32 = arith.constant {handshake.name = "constant1"} 0 : i32
    cf.br ^bb1(%cst, %c0_i32 : f32, i32) {handshake.name = "br0"}
  ^bb1(%0: f32, %1: i32):  // 2 preds: ^bb0, ^bb3
    %cst_0 = arith.constant {handshake.name = "constant8"} 0.000000e+00 : f32
    %2 = arith.extui %1 {handshake.name = "extui0"} : i32 to i64
    %3 = arith.index_cast %2 {handshake.name = "index_cast0"} : i64 to index
    %4 = memref.load %arg0[%3] {handshake.name = "load0"} : memref<1000xf32>
    %5 = arith.cmpf ult, %4, %cst_0 {handshake.name = "cmpf0"} : f32
    cf.cond_br %5, ^bb3(%0 : f32), ^bb2 {handshake.name = "cond_br0"}
  ^bb2:  // pred: ^bb1
    %cst_1 = arith.constant {handshake.name = "constant9"} 3.300000e-01 : f32
    %cst_2 = arith.constant {handshake.name = "constant10"} 2.100000e-01 : f32
    %cst_3 = arith.constant {handshake.name = "constant11"} 0.699999988 : f32
    %cst_4 = arith.constant {handshake.name = "constant12"} 6.400000e-01 : f32
    %6 = arith.addf %4, %cst_4 {handshake.name = "addf0"} : f32
    %7 = arith.mulf %6, %4 {handshake.name = "mulf0"} : f32
    %8 = arith.addf %7, %cst_3 {handshake.name = "addf1"} : f32
    %9 = arith.mulf %8, %4 {handshake.name = "mulf1"} : f32
    %10 = arith.addf %9, %cst_2 {handshake.name = "addf2"} : f32
    %11 = arith.mulf %10, %4 {handshake.name = "mulf2"} : f32
    %12 = arith.addf %11, %cst_1 {handshake.name = "addf3"} : f32
    %13 = arith.mulf %12, %4 {handshake.name = "mulf3"} : f32
    %14 = arith.addf %0, %13 {handshake.name = "addf4"} : f32
    cf.br ^bb3(%14 : f32) {handshake.name = "br1"}
  ^bb3(%15: f32):  // 2 preds: ^bb1, ^bb2
    %c1000_i32 = arith.constant {handshake.name = "constant13"} 1000 : i32
    %c1_i32 = arith.constant {handshake.name = "constant14"} 1 : i32
    %16 = arith.addi %1, %c1_i32 {handshake.name = "addi0"} : i32
    %17 = arith.cmpi ult, %16, %c1000_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %17, ^bb1(%15, %16 : f32, i32), ^bb4(%15 : f32) {handshake.name = "cond_br1"}
  ^bb4(%18: f32):  // pred: ^bb3
    return {handshake.name = "return0"} %18 : f32
  }
}

