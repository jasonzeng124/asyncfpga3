module {
  func.func @mvt_float(%arg0: memref<900xf32> {handshake.arg_name = "A"}, %arg1: memref<30xf32> {handshake.arg_name = "x1"}, %arg2: memref<30xf32> {handshake.arg_name = "x2"}, %arg3: memref<30xf32> {handshake.arg_name = "y1"}, %arg4: memref<30xf32> {handshake.arg_name = "y2"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %c0_i32_0 = arith.constant {handshake.name = "constant8"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.index_cast %1 {handshake.name = "index_cast0"} : i64 to index
    %3 = memref.load %arg1[%2] {handshake.name = "load0"} : memref<30xf32>
    %4 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    cf.br ^bb2(%3, %c0_i32_0 : f32, i32) {handshake.name = "br1"}
  ^bb2(%5: f32, %6: i32):  // 2 preds: ^bb1, ^bb2
    %c30_i32 = arith.constant {handshake.name = "constant9"} 30 : i32
    %c1_i32 = arith.constant {handshake.name = "constant10"} 1 : i32
    %c4_i64 = arith.constant {handshake.name = "constant11"} 4 : i64
    %c3_i64 = arith.constant {handshake.name = "constant12"} 3 : i64
    %c2_i64 = arith.constant {handshake.name = "constant13"} 2 : i64
    %c1_i64 = arith.constant {handshake.name = "constant14"} 1 : i64
    %7 = arith.extui %6 {handshake.name = "extui2"} : i32 to i64
    %8 = arith.shli %4, %c1_i64 {handshake.name = "shli0"} : i64
    %9 = arith.shli %4, %c2_i64 {handshake.name = "shli1"} : i64
    %10 = arith.addi %8, %9 {handshake.name = "addi6"} : i64
    %11 = arith.shli %4, %c3_i64 {handshake.name = "shli2"} : i64
    %12 = arith.shli %4, %c4_i64 {handshake.name = "shli3"} : i64
    %13 = arith.addi %11, %12 {handshake.name = "addi7"} : i64
    %14 = arith.addi %10, %13 {handshake.name = "addi8"} : i64
    %15 = arith.addi %14, %7 {handshake.name = "addi0"} : i64
    %16 = arith.index_cast %15 {handshake.name = "index_cast1"} : i64 to index
    %17 = memref.load %arg0[%16] {handshake.name = "load1"} : memref<900xf32>
    %18 = arith.extui %6 {handshake.name = "extui3"} : i32 to i64
    %19 = arith.index_cast %18 {handshake.name = "index_cast2"} : i64 to index
    %20 = memref.load %arg3[%19] {handshake.name = "load2"} : memref<30xf32>
    %21 = arith.mulf %17, %20 {handshake.name = "mulf0"} : f32
    %22 = arith.addf %5, %21 {handshake.name = "addf0"} : f32
    %23 = arith.addi %6, %c1_i32 {handshake.name = "addi1"} : i32
    %24 = arith.cmpi ult, %23, %c30_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %24, ^bb2(%22, %23 : f32, i32), ^bb3(%22 : f32) {handshake.name = "cond_br0"}
  ^bb3(%25: f32):  // pred: ^bb2
    %c30_i32_1 = arith.constant {handshake.name = "constant15"} 30 : i32
    %c1_i32_2 = arith.constant {handshake.name = "constant16"} 1 : i32
    %c0_i32_3 = arith.constant {handshake.name = "constant17"} 0 : i32
    %26 = arith.extui %0 {handshake.name = "extui4"} : i32 to i64
    %27 = arith.index_cast %26 {handshake.name = "index_cast3"} : i64 to index
    memref.store %25, %arg1[%27] {handshake.name = "store3"} : memref<30xf32>
    %28 = arith.addi %0, %c1_i32_2 {handshake.name = "addi2"} : i32
    %29 = arith.cmpi ult, %28, %c30_i32_1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %29, ^bb1(%28 : i32), ^bb4(%c0_i32_3 : i32) {handshake.name = "cond_br1"}
  ^bb4(%30: i32):  // 2 preds: ^bb3, ^bb6
    %c0_i32_4 = arith.constant {handshake.name = "constant18"} 0 : i32
    %31 = arith.extui %30 {handshake.name = "extui5"} : i32 to i64
    %32 = arith.index_cast %31 {handshake.name = "index_cast4"} : i64 to index
    %33 = memref.load %arg2[%32] {handshake.name = "load4"} : memref<30xf32>
    %34 = arith.extui %30 {handshake.name = "extui6"} : i32 to i64
    cf.br ^bb5(%33, %c0_i32_4 : f32, i32) {handshake.name = "br2"}
  ^bb5(%35: f32, %36: i32):  // 2 preds: ^bb4, ^bb5
    %c30_i32_5 = arith.constant {handshake.name = "constant19"} 30 : i32
    %c1_i32_6 = arith.constant {handshake.name = "constant20"} 1 : i32
    %c4_i64_7 = arith.constant {handshake.name = "constant21"} 4 : i64
    %c3_i64_8 = arith.constant {handshake.name = "constant22"} 3 : i64
    %c2_i64_9 = arith.constant {handshake.name = "constant23"} 2 : i64
    %c1_i64_10 = arith.constant {handshake.name = "constant24"} 1 : i64
    %37 = arith.extui %36 {handshake.name = "extui7"} : i32 to i64
    %38 = arith.shli %37, %c1_i64_10 {handshake.name = "shli4"} : i64
    %39 = arith.shli %37, %c2_i64_9 {handshake.name = "shli5"} : i64
    %40 = arith.addi %38, %39 {handshake.name = "addi9"} : i64
    %41 = arith.shli %37, %c3_i64_8 {handshake.name = "shli6"} : i64
    %42 = arith.shli %37, %c4_i64_7 {handshake.name = "shli7"} : i64
    %43 = arith.addi %41, %42 {handshake.name = "addi10"} : i64
    %44 = arith.addi %40, %43 {handshake.name = "addi11"} : i64
    %45 = arith.addi %44, %34 {handshake.name = "addi3"} : i64
    %46 = arith.index_cast %45 {handshake.name = "index_cast5"} : i64 to index
    %47 = memref.load %arg0[%46] {handshake.name = "load5"} : memref<900xf32>
    %48 = arith.extui %36 {handshake.name = "extui8"} : i32 to i64
    %49 = arith.index_cast %48 {handshake.name = "index_cast6"} : i64 to index
    %50 = memref.load %arg4[%49] {handshake.name = "load6"} : memref<30xf32>
    %51 = arith.mulf %47, %50 {handshake.name = "mulf1"} : f32
    %52 = arith.addf %35, %51 {handshake.name = "addf1"} : f32
    %53 = arith.addi %36, %c1_i32_6 {handshake.name = "addi4"} : i32
    %54 = arith.cmpi ult, %53, %c30_i32_5 {handshake.name = "cmpi2"} : i32
    cf.cond_br %54, ^bb5(%52, %53 : f32, i32), ^bb6(%52 : f32) {handshake.name = "cond_br2"}
  ^bb6(%55: f32):  // pred: ^bb5
    %c30_i32_11 = arith.constant {handshake.name = "constant25"} 30 : i32
    %c1_i32_12 = arith.constant {handshake.name = "constant26"} 1 : i32
    %56 = arith.extui %30 {handshake.name = "extui9"} : i32 to i64
    %57 = arith.index_cast %56 {handshake.name = "index_cast7"} : i64 to index
    memref.store %55, %arg2[%57] {handshake.name = "store7"} : memref<30xf32>
    %58 = arith.addi %30, %c1_i32_12 {handshake.name = "addi5"} : i32
    %59 = arith.cmpi ult, %58, %c30_i32_11 {handshake.name = "cmpi3"} : i32
    cf.cond_br %59, ^bb4(%58 : i32), ^bb7 {handshake.name = "cond_br3"}
  ^bb7:  // pred: ^bb6
    return {handshake.name = "return0"}
  }
}

