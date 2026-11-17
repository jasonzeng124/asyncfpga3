module {
  func.func @syr2k_float(%arg0: memref<900xf32> {handshake.arg_name = "A"}, %arg1: memref<900xf32> {handshake.arg_name = "B"}, %arg2: memref<900xf32> {handshake.arg_name = "C"}, %arg3: f32 {handshake.arg_name = "alpha"}, %arg4: f32 {handshake.arg_name = "beta"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %c0_i32_0 = arith.constant {handshake.name = "constant8"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    cf.br ^bb2(%c0_i32_0 : i32) {handshake.name = "br1"}
  ^bb2(%2: i32):  // 2 preds: ^bb1, ^bb2
    %c10_i32 = arith.constant {handshake.name = "constant9"} 10 : i32
    %c1_i32 = arith.constant {handshake.name = "constant10"} 1 : i32
    %c4_i64 = arith.constant {handshake.name = "constant11"} 4 : i64
    %c3_i64 = arith.constant {handshake.name = "constant12"} 3 : i64
    %c2_i64 = arith.constant {handshake.name = "constant13"} 2 : i64
    %c1_i64 = arith.constant {handshake.name = "constant14"} 1 : i64
    %3 = arith.extui %2 {handshake.name = "extui1"} : i32 to i64
    %4 = arith.shli %1, %c1_i64 {handshake.name = "shli0"} : i64
    %5 = arith.shli %1, %c2_i64 {handshake.name = "shli1"} : i64
    %6 = arith.addi %4, %5 {handshake.name = "addi12"} : i64
    %7 = arith.shli %1, %c3_i64 {handshake.name = "shli2"} : i64
    %8 = arith.shli %1, %c4_i64 {handshake.name = "shli3"} : i64
    %9 = arith.addi %7, %8 {handshake.name = "addi13"} : i64
    %10 = arith.addi %6, %9 {handshake.name = "addi14"} : i64
    %11 = arith.addi %10, %3 {handshake.name = "addi0"} : i64
    %12 = arith.index_cast %11 {handshake.name = "index_cast0"} : i64 to index
    %13 = memref.load %arg2[%12] {handshake.name = "load0"} : memref<900xf32>
    %14 = arith.mulf %13, %arg4 {handshake.name = "mulf0"} : f32
    %15 = arith.index_cast %11 {handshake.name = "index_cast1"} : i64 to index
    memref.store %14, %arg2[%15] {handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store7", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : memref<900xf32>
    %16 = arith.addi %2, %c1_i32 {handshake.name = "addi1"} : i32
    %17 = arith.cmpi ult, %16, %c10_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %17, ^bb2(%16 : i32), ^bb3 {handshake.name = "cond_br0"}
  ^bb3:  // pred: ^bb2
    %c10_i32_1 = arith.constant {handshake.name = "constant15"} 10 : i32
    %c1_i32_2 = arith.constant {handshake.name = "constant16"} 1 : i32
    %c0_i32_3 = arith.constant {handshake.name = "constant17"} 0 : i32
    %18 = arith.addi %0, %c1_i32_2 {handshake.name = "addi2"} : i32
    %19 = arith.cmpi ult, %18, %c10_i32_1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %19, ^bb1(%18 : i32), ^bb4(%c0_i32_3 : i32) {handshake.name = "cond_br1"}
  ^bb4(%20: i32):  // 2 preds: ^bb3, ^bb8
    %c0_i32_4 = arith.constant {handshake.name = "constant18"} 0 : i32
    %21 = arith.extui %20 {handshake.name = "extui2"} : i32 to i64
    %22 = arith.extui %20 {handshake.name = "extui3"} : i32 to i64
    %23 = arith.extui %20 {handshake.name = "extui4"} : i32 to i64
    %24 = arith.extui %20 {handshake.name = "extui5"} : i32 to i64
    cf.br ^bb5(%c0_i32_4 : i32) {handshake.name = "br2"}
  ^bb5(%25: i32):  // 2 preds: ^bb4, ^bb7
    %c0_i32_5 = arith.constant {handshake.name = "constant19"} 0 : i32
    %c4_i64_6 = arith.constant {handshake.name = "constant20"} 4 : i64
    %c3_i64_7 = arith.constant {handshake.name = "constant21"} 3 : i64
    %c2_i64_8 = arith.constant {handshake.name = "constant22"} 2 : i64
    %c1_i64_9 = arith.constant {handshake.name = "constant23"} 1 : i64
    %26 = arith.extui %25 {handshake.name = "extui6"} : i32 to i64
    %27 = arith.shli %21, %c1_i64_9 {handshake.name = "shli4"} : i64
    %28 = arith.shli %21, %c2_i64_8 {handshake.name = "shli5"} : i64
    %29 = arith.addi %27, %28 {handshake.name = "addi15"} : i64
    %30 = arith.shli %21, %c3_i64_7 {handshake.name = "shli6"} : i64
    %31 = arith.shli %21, %c4_i64_6 {handshake.name = "shli7"} : i64
    %32 = arith.addi %30, %31 {handshake.name = "addi16"} : i64
    %33 = arith.addi %29, %32 {handshake.name = "addi17"} : i64
    %34 = arith.addi %33, %26 {handshake.name = "addi3"} : i64
    %35 = arith.index_cast %34 {handshake.name = "index_cast2"} : i64 to index
    %36 = memref.load %arg2[%35] {handshake.name = "load2"} : memref<900xf32>
    %37 = arith.extui %25 {handshake.name = "extui7"} : i32 to i64
    %38 = arith.extui %25 {handshake.name = "extui8"} : i32 to i64
    cf.br ^bb6(%36, %c0_i32_5 : f32, i32) {handshake.name = "br3"}
  ^bb6(%39: f32, %40: i32):  // 2 preds: ^bb5, ^bb6
    %c10_i32_10 = arith.constant {handshake.name = "constant24"} 10 : i32
    %c1_i32_11 = arith.constant {handshake.name = "constant25"} 1 : i32
    %c4_i64_12 = arith.constant {handshake.name = "constant26"} 4 : i64
    %c3_i64_13 = arith.constant {handshake.name = "constant27"} 3 : i64
    %c2_i64_14 = arith.constant {handshake.name = "constant28"} 2 : i64
    %c1_i64_15 = arith.constant {handshake.name = "constant29"} 1 : i64
    %41 = arith.extui %40 {handshake.name = "extui9"} : i32 to i64
    %42 = arith.shli %22, %c1_i64_15 {handshake.name = "shli8"} : i64
    %43 = arith.shli %22, %c2_i64_14 {handshake.name = "shli9"} : i64
    %44 = arith.addi %42, %43 {handshake.name = "addi18"} : i64
    %45 = arith.shli %22, %c3_i64_13 {handshake.name = "shli10"} : i64
    %46 = arith.shli %22, %c4_i64_12 {handshake.name = "shli11"} : i64
    %47 = arith.addi %45, %46 {handshake.name = "addi19"} : i64
    %48 = arith.addi %44, %47 {handshake.name = "addi20"} : i64
    %49 = arith.addi %48, %41 {handshake.name = "addi4"} : i64
    %50 = arith.index_cast %49 {handshake.name = "index_cast3"} : i64 to index
    %51 = memref.load %arg0[%50] {handshake.name = "load3"} : memref<900xf32>
    %52 = arith.mulf %51, %arg3 {handshake.name = "mulf1"} : f32
    %53 = arith.extui %40 {handshake.name = "extui10"} : i32 to i64
    %54 = arith.shli %37, %c1_i64_15 {handshake.name = "shli12"} : i64
    %55 = arith.shli %37, %c2_i64_14 {handshake.name = "shli13"} : i64
    %56 = arith.addi %54, %55 {handshake.name = "addi21"} : i64
    %57 = arith.shli %37, %c3_i64_13 {handshake.name = "shli14"} : i64
    %58 = arith.shli %37, %c4_i64_12 {handshake.name = "shli15"} : i64
    %59 = arith.addi %57, %58 {handshake.name = "addi22"} : i64
    %60 = arith.addi %56, %59 {handshake.name = "addi23"} : i64
    %61 = arith.addi %60, %53 {handshake.name = "addi5"} : i64
    %62 = arith.index_cast %61 {handshake.name = "index_cast4"} : i64 to index
    %63 = memref.load %arg1[%62] {handshake.name = "load4"} : memref<900xf32>
    %64 = arith.mulf %52, %63 {handshake.name = "mulf2"} : f32
    %65 = arith.addf %39, %64 {handshake.name = "addf0"} : f32
    %66 = arith.extui %40 {handshake.name = "extui11"} : i32 to i64
    %67 = arith.shli %23, %c1_i64_15 {handshake.name = "shli16"} : i64
    %68 = arith.shli %23, %c2_i64_14 {handshake.name = "shli17"} : i64
    %69 = arith.addi %67, %68 {handshake.name = "addi24"} : i64
    %70 = arith.shli %23, %c3_i64_13 {handshake.name = "shli18"} : i64
    %71 = arith.shli %23, %c4_i64_12 {handshake.name = "shli19"} : i64
    %72 = arith.addi %70, %71 {handshake.name = "addi25"} : i64
    %73 = arith.addi %69, %72 {handshake.name = "addi26"} : i64
    %74 = arith.addi %73, %66 {handshake.name = "addi6"} : i64
    %75 = arith.index_cast %74 {handshake.name = "index_cast5"} : i64 to index
    %76 = memref.load %arg1[%75] {handshake.name = "load5"} : memref<900xf32>
    %77 = arith.mulf %76, %arg3 {handshake.name = "mulf3"} : f32
    %78 = arith.extui %40 {handshake.name = "extui12"} : i32 to i64
    %79 = arith.shli %38, %c1_i64_15 {handshake.name = "shli20"} : i64
    %80 = arith.shli %38, %c2_i64_14 {handshake.name = "shli21"} : i64
    %81 = arith.addi %79, %80 {handshake.name = "addi27"} : i64
    %82 = arith.shli %38, %c3_i64_13 {handshake.name = "shli22"} : i64
    %83 = arith.shli %38, %c4_i64_12 {handshake.name = "shli23"} : i64
    %84 = arith.addi %82, %83 {handshake.name = "addi28"} : i64
    %85 = arith.addi %81, %84 {handshake.name = "addi29"} : i64
    %86 = arith.addi %85, %78 {handshake.name = "addi7"} : i64
    %87 = arith.index_cast %86 {handshake.name = "index_cast6"} : i64 to index
    %88 = memref.load %arg0[%87] {handshake.name = "load6"} : memref<900xf32>
    %89 = arith.mulf %77, %88 {handshake.name = "mulf4"} : f32
    %90 = arith.addf %65, %89 {handshake.name = "addf1"} : f32
    %91 = arith.addi %40, %c1_i32_11 {handshake.name = "addi8"} : i32
    %92 = arith.cmpi ult, %91, %c10_i32_10 {handshake.name = "cmpi2"} : i32
    cf.cond_br %92, ^bb6(%90, %91 : f32, i32), ^bb7(%90 : f32) {handshake.name = "cond_br2"}
  ^bb7(%93: f32):  // pred: ^bb6
    %c10_i32_16 = arith.constant {handshake.name = "constant30"} 10 : i32
    %c1_i32_17 = arith.constant {handshake.name = "constant31"} 1 : i32
    %c4_i64_18 = arith.constant {handshake.name = "constant32"} 4 : i64
    %c3_i64_19 = arith.constant {handshake.name = "constant33"} 3 : i64
    %c2_i64_20 = arith.constant {handshake.name = "constant34"} 2 : i64
    %c1_i64_21 = arith.constant {handshake.name = "constant35"} 1 : i64
    %94 = arith.extui %25 {handshake.name = "extui13"} : i32 to i64
    %95 = arith.shli %24, %c1_i64_21 {handshake.name = "shli24"} : i64
    %96 = arith.shli %24, %c2_i64_20 {handshake.name = "shli25"} : i64
    %97 = arith.addi %95, %96 {handshake.name = "addi30"} : i64
    %98 = arith.shli %24, %c3_i64_19 {handshake.name = "shli26"} : i64
    %99 = arith.shli %24, %c4_i64_18 {handshake.name = "shli27"} : i64
    %100 = arith.addi %98, %99 {handshake.name = "addi31"} : i64
    %101 = arith.addi %97, %100 {handshake.name = "addi32"} : i64
    %102 = arith.addi %101, %94 {handshake.name = "addi9"} : i64
    %103 = arith.index_cast %102 {handshake.name = "index_cast7"} : i64 to index
    memref.store %93, %arg2[%103] {handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store7"} : memref<900xf32>
    %104 = arith.addi %25, %c1_i32_17 {handshake.name = "addi10"} : i32
    %105 = arith.cmpi ult, %104, %c10_i32_16 {handshake.name = "cmpi3"} : i32
    cf.cond_br %105, ^bb5(%104 : i32), ^bb8 {handshake.name = "cond_br3"}
  ^bb8:  // pred: ^bb7
    %c10_i32_22 = arith.constant {handshake.name = "constant36"} 10 : i32
    %c1_i32_23 = arith.constant {handshake.name = "constant37"} 1 : i32
    %106 = arith.addi %20, %c1_i32_23 {handshake.name = "addi11"} : i32
    %107 = arith.cmpi ult, %106, %c10_i32_22 {handshake.name = "cmpi4"} : i32
    cf.cond_br %107, ^bb4(%106 : i32), ^bb9 {handshake.name = "cond_br4"}
  ^bb9:  // pred: ^bb8
    return {handshake.name = "return0"}
  }
}

