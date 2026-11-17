module {
  func.func @cordic(%arg0: f32 {handshake.arg_name = "theta"}, %arg1: memref<2xf32> {handshake.arg_name = "a"}, %arg2: memref<1000xf32> {handshake.arg_name = "cordic_phase"}, %arg3: f32 {handshake.arg_name = "current_cos"}, %arg4: f32 {handshake.arg_name = "current_sin"}) -> f32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %cst = arith.constant {handshake.name = "constant1"} 1.000000e+00 : f32
    cf.br ^bb1(%arg0, %c0_i32, %cst, %arg3, %arg4 : f32, i32, f32, f32, f32) {handshake.name = "br0"}
  ^bb1(%0: f32, %1: i32, %2: f32, %3: f32, %4: f32):  // 2 preds: ^bb0, ^bb1
    %c1000_i32 = arith.constant {handshake.name = "constant9"} 1000 : i32
    %c1_i32 = arith.constant {handshake.name = "constant10"} 1 : i32
    %cst_0 = arith.constant {handshake.name = "constant11"} -1.000000e+00 : f32
    %cst_1 = arith.constant {handshake.name = "constant12"} 0.000000e+00 : f32
    %cst_2 = arith.constant {handshake.name = "constant13"} 5.000000e-01 : f32
    %cst_3 = arith.constant {handshake.name = "constant14"} 1.000000e+00 : f32
    %5 = arith.mulf %2, %cst_2 {handshake.name = "mulf0"} : f32
    %6 = arith.cmpf olt, %0, %cst_1 {handshake.name = "cmpf0"} : f32
    %7 = arith.select %6, %cst_0, %cst_3 {handshake.name = "select0"} : f32
    %8 = arith.extui %1 {handshake.name = "extui0"} : i32 to i64
    %9 = arith.index_cast %8 {handshake.name = "index_cast0"} : i64 to index
    %10 = memref.load %arg2[%9] {handshake.name = "load0"} : memref<1000xf32>
    %11 = arith.mulf %7, %10 {handshake.name = "mulf1"} : f32
    %12 = arith.subf %0, %11 {handshake.name = "subf0"} : f32
    %13 = arith.mulf %3, %7 {handshake.name = "mulf2"} : f32
    %14 = arith.mulf %13, %2 {handshake.name = "mulf3"} : f32
    %15 = arith.addf %14, %4 {handshake.name = "addf0"} : f32
    %16 = arith.mulf %4, %7 {handshake.name = "mulf4"} : f32
    %17 = arith.mulf %16, %2 {handshake.name = "mulf5"} : f32
    %18 = arith.subf %3, %17 {handshake.name = "subf1"} : f32
    %19 = arith.addi %1, %c1_i32 {handshake.name = "addi0"} : i32
    %20 = arith.cmpi ult, %19, %c1000_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %20, ^bb1(%12, %19, %5, %18, %15 : f32, i32, f32, f32, f32), ^bb2(%15, %18, %12 : f32, f32, f32) {handshake.name = "cond_br0"}
  ^bb2(%21: f32, %22: f32, %23: f32):  // pred: ^bb1
    %c0 = arith.constant {handshake.name = "constant15"} 0 : index
    %c1 = arith.constant {handshake.name = "constant16"} 1 : index
    memref.store %22, %arg1[%c0] {handshake.name = "store1"} : memref<2xf32>
    memref.store %21, %arg1[%c1] {handshake.name = "store2"} : memref<2xf32>
    return {handshake.name = "return0"} %23 : f32
  }
}

