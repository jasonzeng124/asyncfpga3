module {
  func.func @gesummv_float(%arg0: f32 {handshake.arg_name = "alpha"}, %arg1: f32 {handshake.arg_name = "beta"}, %arg2: memref<900xf32> {handshake.arg_name = "A"}, %arg3: memref<900xf32> {handshake.arg_name = "B"}, %arg4: memref<30xf32> {handshake.arg_name = "tmp"}, %arg5: memref<30xf32> {handshake.arg_name = "y"}, %arg6: memref<30xf32> {handshake.arg_name = "x"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %cst = arith.constant {handshake.name = "constant9"} 0.000000e+00 : f32
    %c0_i32_0 = arith.constant {handshake.name = "constant10"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    cf.br ^bb2(%cst, %cst, %c0_i32_0 : f32, f32, i32) {handshake.name = "br1"}
  ^bb2(%3: f32, %4: f32, %5: i32):  // 2 preds: ^bb1, ^bb2
    %c30_i32 = arith.constant {handshake.name = "constant11"} 30 : i32
    %c1_i32 = arith.constant {handshake.name = "constant12"} 1 : i32
    %c4_i64 = arith.constant {handshake.name = "constant13"} 4 : i64
    %c3_i64 = arith.constant {handshake.name = "constant14"} 3 : i64
    %c2_i64 = arith.constant {handshake.name = "constant15"} 2 : i64
    %c1_i64 = arith.constant {handshake.name = "constant16"} 1 : i64
    %6 = arith.extui %5 {handshake.name = "extui2"} : i32 to i64
    %7 = arith.shli %1, %c1_i64 {handshake.name = "shli0"} : i64
    %8 = arith.shli %1, %c2_i64 {handshake.name = "shli1"} : i64
    %9 = arith.addi %7, %8 {handshake.name = "addi4"} : i64
    %10 = arith.shli %1, %c3_i64 {handshake.name = "shli2"} : i64
    %11 = arith.shli %1, %c4_i64 {handshake.name = "shli3"} : i64
    %12 = arith.addi %10, %11 {handshake.name = "addi5"} : i64
    %13 = arith.addi %9, %12 {handshake.name = "addi6"} : i64
    %14 = arith.addi %13, %6 {handshake.name = "addi0"} : i64
    %15 = arith.index_cast %14 {handshake.name = "index_cast0"} : i64 to index
    %16 = memref.load %arg3[%15] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : memref<900xf32>
    %17 = arith.extui %5 {handshake.name = "extui3"} : i32 to i64
    %18 = arith.index_cast %17 {handshake.name = "index_cast1"} : i64 to index
    %19 = memref.load %arg6[%18] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : memref<30xf32>
    %20 = arith.mulf %16, %19 {handshake.name = "mulf0"} : f32
    %21 = arith.addf %20, %3 {handshake.name = "addf0"} : f32
    %22 = arith.extui %5 {handshake.name = "extui4"} : i32 to i64
    %23 = arith.shli %2, %c1_i64 {handshake.name = "shli4"} : i64
    %24 = arith.shli %2, %c2_i64 {handshake.name = "shli5"} : i64
    %25 = arith.addi %23, %24 {handshake.name = "addi7"} : i64
    %26 = arith.shli %2, %c3_i64 {handshake.name = "shli6"} : i64
    %27 = arith.shli %2, %c4_i64 {handshake.name = "shli7"} : i64
    %28 = arith.addi %26, %27 {handshake.name = "addi8"} : i64
    %29 = arith.addi %25, %28 {handshake.name = "addi9"} : i64
    %30 = arith.addi %29, %22 {handshake.name = "addi1"} : i64
    %31 = arith.index_cast %30 {handshake.name = "index_cast2"} : i64 to index
    %32 = memref.load %arg2[%31] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load2"} : memref<900xf32>
    %33 = arith.mulf %32, %19 {handshake.name = "mulf1"} : f32
    %34 = arith.addf %33, %4 {handshake.name = "addf1"} : f32
    %35 = arith.addi %5, %c1_i32 {handshake.name = "addi2"} : i32
    %36 = arith.cmpi ult, %35, %c30_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %36, ^bb2(%21, %34, %35 : f32, f32, i32), ^bb3(%34, %21 : f32, f32) {handshake.name = "cond_br0"}
  ^bb3(%37: f32, %38: f32):  // pred: ^bb2
    %c30_i32_1 = arith.constant {handshake.name = "constant17"} 30 : i32
    %c1_i32_2 = arith.constant {handshake.name = "constant18"} 1 : i32
    %39 = arith.extui %0 {handshake.name = "extui5"} : i32 to i64
    %40 = arith.index_cast %39 {handshake.name = "index_cast3"} : i64 to index
    memref.store %37, %arg4[%40] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store3"} : memref<30xf32>
    %41 = arith.mulf %37, %arg0 {handshake.name = "mulf2"} : f32
    %42 = arith.mulf %38, %arg1 {handshake.name = "mulf3"} : f32
    %43 = arith.addf %41, %42 {handshake.name = "addf2"} : f32
    %44 = arith.extui %0 {handshake.name = "extui6"} : i32 to i64
    %45 = arith.index_cast %44 {handshake.name = "index_cast4"} : i64 to index
    memref.store %43, %arg5[%45] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store4"} : memref<30xf32>
    %46 = arith.addi %0, %c1_i32_2 {handshake.name = "addi3"} : i32
    %47 = arith.cmpi ult, %46, %c30_i32_1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %47, ^bb1(%46 : i32), ^bb4 {handshake.name = "cond_br1"}
  ^bb4:  // pred: ^bb3
    return {handshake.name = "return0"}
  }
}

