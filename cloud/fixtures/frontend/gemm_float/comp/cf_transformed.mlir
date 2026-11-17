module {
  func.func @gemm_float(%arg0: f32 {handshake.arg_name = "alpha"}, %arg1: f32 {handshake.arg_name = "beta"}, %arg2: memref<900xf32> {handshake.arg_name = "A"}, %arg3: memref<900xf32> {handshake.arg_name = "B"}, %arg4: memref<900xf32> {handshake.arg_name = "C"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb5
    %c0_i32_0 = arith.constant {handshake.name = "constant8"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %3 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    cf.br ^bb2(%c0_i32_0 : i32) {handshake.name = "br1"}
  ^bb2(%4: i32):  // 2 preds: ^bb1, ^bb4
    %c0_i32_1 = arith.constant {handshake.name = "constant9"} 0 : i32
    %c4_i64 = arith.constant {handshake.name = "constant10"} 4 : i64
    %c3_i64 = arith.constant {handshake.name = "constant11"} 3 : i64
    %c2_i64 = arith.constant {handshake.name = "constant12"} 2 : i64
    %c1_i64 = arith.constant {handshake.name = "constant13"} 1 : i64
    %5 = arith.extui %4 {handshake.name = "extui3"} : i32 to i64
    %6 = arith.shli %1, %c1_i64 {handshake.name = "shli0"} : i64
    %7 = arith.shli %1, %c2_i64 {handshake.name = "shli1"} : i64
    %8 = arith.addi %6, %7 {handshake.name = "addi7"} : i64
    %9 = arith.shli %1, %c3_i64 {handshake.name = "shli2"} : i64
    %10 = arith.shli %1, %c4_i64 {handshake.name = "shli3"} : i64
    %11 = arith.addi %9, %10 {handshake.name = "addi8"} : i64
    %12 = arith.addi %8, %11 {handshake.name = "addi9"} : i64
    %13 = arith.addi %12, %5 {handshake.name = "addi0"} : i64
    %14 = arith.index_cast %13 {handshake.name = "index_cast0"} : i64 to index
    %15 = memref.load %arg4[%14] {handshake.name = "load0"} : memref<900xf32>
    %16 = arith.mulf %15, %arg1 {handshake.name = "mulf0"} : f32
    %17 = arith.extui %4 {handshake.name = "extui4"} : i32 to i64
    cf.br ^bb3(%16, %c0_i32_1 : f32, i32) {handshake.name = "br2"}
  ^bb3(%18: f32, %19: i32):  // 2 preds: ^bb2, ^bb3
    %c20_i32 = arith.constant {handshake.name = "constant14"} 20 : i32
    %c1_i32 = arith.constant {handshake.name = "constant15"} 1 : i32
    %c4_i64_2 = arith.constant {handshake.name = "constant16"} 4 : i64
    %c3_i64_3 = arith.constant {handshake.name = "constant17"} 3 : i64
    %c2_i64_4 = arith.constant {handshake.name = "constant18"} 2 : i64
    %c1_i64_5 = arith.constant {handshake.name = "constant19"} 1 : i64
    %20 = arith.extui %19 {handshake.name = "extui5"} : i32 to i64
    %21 = arith.shli %2, %c1_i64_5 {handshake.name = "shli4"} : i64
    %22 = arith.shli %2, %c2_i64_4 {handshake.name = "shli5"} : i64
    %23 = arith.addi %21, %22 {handshake.name = "addi10"} : i64
    %24 = arith.shli %2, %c3_i64_3 {handshake.name = "shli6"} : i64
    %25 = arith.shli %2, %c4_i64_2 {handshake.name = "shli7"} : i64
    %26 = arith.addi %24, %25 {handshake.name = "addi11"} : i64
    %27 = arith.addi %23, %26 {handshake.name = "addi12"} : i64
    %28 = arith.addi %27, %20 {handshake.name = "addi1"} : i64
    %29 = arith.index_cast %28 {handshake.name = "index_cast1"} : i64 to index
    %30 = memref.load %arg2[%29] {handshake.name = "load1"} : memref<900xf32>
    %31 = arith.mulf %30, %arg0 {handshake.name = "mulf1"} : f32
    %32 = arith.extui %19 {handshake.name = "extui6"} : i32 to i64
    %33 = arith.shli %32, %c1_i64_5 {handshake.name = "shli8"} : i64
    %34 = arith.shli %32, %c2_i64_4 {handshake.name = "shli9"} : i64
    %35 = arith.addi %33, %34 {handshake.name = "addi13"} : i64
    %36 = arith.shli %32, %c3_i64_3 {handshake.name = "shli10"} : i64
    %37 = arith.shli %32, %c4_i64_2 {handshake.name = "shli11"} : i64
    %38 = arith.addi %36, %37 {handshake.name = "addi14"} : i64
    %39 = arith.addi %35, %38 {handshake.name = "addi15"} : i64
    %40 = arith.addi %39, %17 {handshake.name = "addi2"} : i64
    %41 = arith.index_cast %40 {handshake.name = "index_cast2"} : i64 to index
    %42 = memref.load %arg3[%41] {handshake.name = "load2"} : memref<900xf32>
    %43 = arith.mulf %31, %42 {handshake.name = "mulf2"} : f32
    %44 = arith.addf %18, %43 {handshake.name = "addf0"} : f32
    %45 = arith.addi %19, %c1_i32 {handshake.name = "addi3"} : i32
    %46 = arith.cmpi ult, %45, %c20_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %46, ^bb3(%44, %45 : f32, i32), ^bb4(%44 : f32) {handshake.name = "cond_br0"}
  ^bb4(%47: f32):  // pred: ^bb3
    %c20_i32_6 = arith.constant {handshake.name = "constant20"} 20 : i32
    %c1_i32_7 = arith.constant {handshake.name = "constant21"} 1 : i32
    %c4_i64_8 = arith.constant {handshake.name = "constant22"} 4 : i64
    %c3_i64_9 = arith.constant {handshake.name = "constant23"} 3 : i64
    %c2_i64_10 = arith.constant {handshake.name = "constant24"} 2 : i64
    %c1_i64_11 = arith.constant {handshake.name = "constant25"} 1 : i64
    %48 = arith.extui %4 {handshake.name = "extui7"} : i32 to i64
    %49 = arith.shli %3, %c1_i64_11 {handshake.name = "shli12"} : i64
    %50 = arith.shli %3, %c2_i64_10 {handshake.name = "shli13"} : i64
    %51 = arith.addi %49, %50 {handshake.name = "addi16"} : i64
    %52 = arith.shli %3, %c3_i64_9 {handshake.name = "shli14"} : i64
    %53 = arith.shli %3, %c4_i64_8 {handshake.name = "shli15"} : i64
    %54 = arith.addi %52, %53 {handshake.name = "addi17"} : i64
    %55 = arith.addi %51, %54 {handshake.name = "addi18"} : i64
    %56 = arith.addi %55, %48 {handshake.name = "addi4"} : i64
    %57 = arith.index_cast %56 {handshake.name = "index_cast3"} : i64 to index
    memref.store %47, %arg4[%57] {handshake.name = "store3"} : memref<900xf32>
    %58 = arith.addi %4, %c1_i32_7 {handshake.name = "addi5"} : i32
    %59 = arith.cmpi ult, %58, %c20_i32_6 {handshake.name = "cmpi1"} : i32
    cf.cond_br %59, ^bb2(%58 : i32), ^bb5 {handshake.name = "cond_br1"}
  ^bb5:  // pred: ^bb4
    %c20_i32_12 = arith.constant {handshake.name = "constant26"} 20 : i32
    %c1_i32_13 = arith.constant {handshake.name = "constant27"} 1 : i32
    %60 = arith.addi %0, %c1_i32_13 {handshake.name = "addi6"} : i32
    %61 = arith.cmpi ult, %60, %c20_i32_12 {handshake.name = "cmpi2"} : i32
    cf.cond_br %61, ^bb1(%60 : i32), ^bb6 {handshake.name = "cond_br2"}
  ^bb6:  // pred: ^bb5
    return {handshake.name = "return0"}
  }
}

