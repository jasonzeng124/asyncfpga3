module {
  memref.global "private" constant @__const.main.A : memref<9xf32> = dense<[1.000000e+00, 3.000000e+00, 5.000000e+00, 2.000000e+00, 4.000000e+00, 7.000000e+00, 1.000000e+00, 1.000000e+00, 0.000000e+00]> {alignment = 16 : i64, handshake.name = "global0"}
  func.func @lu(%arg0: memref<9xf32> {handshake.arg_name = "A"}, %arg1: memref<9xf32> {handshake.arg_name = "L"}, %arg2: memref<9xf32> {handshake.arg_name = "U"}, %arg3: memref<9xf32> {handshake.arg_name = "P"}, %arg4: memref<9xf32> {handshake.arg_name = "A_prime"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %c0_i32_0 = arith.constant {handshake.name = "constant7"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    cf.br ^bb2(%c0_i32_0 : i32) {handshake.name = "br1"}
  ^bb2(%2: i32):  // 2 preds: ^bb1, ^bb2
    %c3_i32 = arith.constant {handshake.name = "constant8"} 3 : i32
    %c1_i32 = arith.constant {handshake.name = "constant9"} 1 : i32
    %c1_i64 = arith.constant {handshake.name = "constant10"} 1 : i64
    %3 = arith.cmpi eq, %0, %2 {handshake.name = "cmpi0"} : i32
    %4 = arith.uitofp %3 {handshake.name = "uitofp0"} : i1 to f32
    %5 = arith.extui %2 {handshake.name = "extui1"} : i32 to i64
    %6 = arith.shli %1, %c1_i64 {handshake.name = "shli0"} : i64
    %7 = arith.addi %1, %6 {handshake.name = "addi33"} : i64
    %8 = arith.addi %7, %5 {handshake.name = "addi0"} : i64
    %9 = arith.index_cast %8 {handshake.name = "index_cast0"} : i64 to index
    memref.store %4, %arg3[%9] {handshake.deps = #handshake<deps[{dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load8", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store6", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store0"} : memref<9xf32>
    %10 = arith.addi %2, %c1_i32 {handshake.name = "addi1"} : i32
    %11 = arith.cmpi ult, %10, %c3_i32 {handshake.name = "cmpi1"} : i32
    cf.cond_br %11, ^bb2(%10 : i32), ^bb3 {handshake.name = "cond_br0"}
  ^bb3:  // pred: ^bb2
    %c3_i32_1 = arith.constant {handshake.name = "constant11"} 3 : i32
    %c1_i32_2 = arith.constant {handshake.name = "constant12"} 1 : i32
    %c0_i32_3 = arith.constant {handshake.name = "constant13"} 0 : i32
    %12 = arith.addi %0, %c1_i32_2 {handshake.name = "addi2"} : i32
    %13 = arith.cmpi ult, %12, %c3_i32_1 {handshake.name = "cmpi2"} : i32
    cf.cond_br %13, ^bb1(%12 : i32), ^bb4(%c0_i32_3 : i32) {handshake.name = "cond_br1"}
  ^bb4(%14: i32):  // 2 preds: ^bb3, ^bb9
    cf.br ^bb5(%14, %14 : i32, i32) {handshake.name = "br2"}
  ^bb5(%15: i32, %16: i32):  // 2 preds: ^bb4, ^bb5
    %c3_i32_4 = arith.constant {handshake.name = "constant14"} 3 : i32
    %c1_i32_5 = arith.constant {handshake.name = "constant15"} 1 : i32
    %c1_i64_6 = arith.constant {handshake.name = "constant16"} 1 : i64
    %17 = arith.extui %16 {handshake.name = "extui2"} : i32 to i64
    %18 = arith.extui %14 {handshake.name = "extui3"} : i32 to i64
    %19 = arith.shli %17, %c1_i64_6 {handshake.name = "shli1"} : i64
    %20 = arith.addi %17, %19 {handshake.name = "addi34"} : i64
    %21 = arith.addi %20, %18 {handshake.name = "addi3"} : i64
    %22 = arith.index_cast %21 {handshake.name = "index_cast1"} : i64 to index
    %23 = memref.load %arg0[%22] {handshake.name = "load1"} : memref<9xf32>
    %24 = math.absf %23 {handshake.name = "absf0"} : f32
    %25 = arith.extsi %15 {handshake.name = "extsi0"} : i32 to i64
    %26 = arith.extui %14 {handshake.name = "extui4"} : i32 to i64
    %27 = arith.shli %25, %c1_i64_6 {handshake.name = "shli2"} : i64
    %28 = arith.addi %25, %27 {handshake.name = "addi35"} : i64
    %29 = arith.addi %28, %26 {handshake.name = "addi4"} : i64
    %30 = arith.index_cast %29 {handshake.name = "index_cast2"} : i64 to index
    %31 = memref.load %arg0[%30] {handshake.name = "load2"} : memref<9xf32>
    %32 = math.absf %31 {handshake.name = "absf1"} : f32
    %33 = arith.cmpf ogt, %24, %32 {handshake.name = "cmpf0"} : f32
    %34 = arith.select %33, %16, %15 {handshake.name = "select0"} : i32
    %35 = arith.addi %16, %c1_i32_5 {handshake.name = "addi5"} : i32
    %36 = arith.cmpi ult, %35, %c3_i32_4 {handshake.name = "cmpi3"} : i32
    cf.cond_br %36, ^bb5(%34, %35 : i32, i32), ^bb6(%34 : i32) {handshake.name = "cond_br2"}
  ^bb6(%37: i32):  // pred: ^bb5
    %38 = arith.cmpi eq, %37, %14 {handshake.name = "cmpi4"} : i32
    cf.cond_br %38, ^bb9, ^bb7 {handshake.name = "cond_br3"}
  ^bb7:  // pred: ^bb6
    %c0_i32_7 = arith.constant {handshake.name = "constant17"} 0 : i32
    %39 = arith.extui %14 {handshake.name = "extui5"} : i32 to i64
    %40 = arith.extsi %37 {handshake.name = "extsi1"} : i32 to i64
    %41 = arith.extui %14 {handshake.name = "extui6"} : i32 to i64
    %42 = arith.extsi %37 {handshake.name = "extsi2"} : i32 to i64
    cf.br ^bb8(%c0_i32_7 : i32) {handshake.name = "br3"}
  ^bb8(%43: i32):  // 2 preds: ^bb7, ^bb8
    %c3_i32_8 = arith.constant {handshake.name = "constant18"} 3 : i32
    %c1_i32_9 = arith.constant {handshake.name = "constant19"} 1 : i32
    %c1_i64_10 = arith.constant {handshake.name = "constant20"} 1 : i64
    %44 = arith.extui %43 {handshake.name = "extui7"} : i32 to i64
    %45 = arith.shli %39, %c1_i64_10 {handshake.name = "shli3"} : i64
    %46 = arith.addi %39, %45 {handshake.name = "addi36"} : i64
    %47 = arith.addi %46, %44 {handshake.name = "addi6"} : i64
    %48 = arith.index_cast %47 {handshake.name = "index_cast3"} : i64 to index
    %49 = memref.load %arg3[%48] {handshake.name = "load3"} : memref<9xf32>
    %50 = arith.fptosi %49 {handshake.name = "fptosi0"} : f32 to i32
    %51 = arith.extui %43 {handshake.name = "extui8"} : i32 to i64
    %52 = arith.shli %40, %c1_i64_10 {handshake.name = "shli4"} : i64
    %53 = arith.addi %40, %52 {handshake.name = "addi37"} : i64
    %54 = arith.addi %53, %51 {handshake.name = "addi7"} : i64
    %55 = arith.index_cast %54 {handshake.name = "index_cast4"} : i64 to index
    %56 = memref.load %arg3[%55] {handshake.name = "load4"} : memref<9xf32>
    %57 = arith.extui %43 {handshake.name = "extui9"} : i32 to i64
    %58 = arith.shli %41, %c1_i64_10 {handshake.name = "shli5"} : i64
    %59 = arith.addi %41, %58 {handshake.name = "addi38"} : i64
    %60 = arith.addi %59, %57 {handshake.name = "addi8"} : i64
    %61 = arith.index_cast %60 {handshake.name = "index_cast5"} : i64 to index
    memref.store %56, %arg3[%61] {handshake.deps = #handshake<deps[{dstAccess : "store0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load8", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store6", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : memref<9xf32>
    %62 = arith.sitofp %50 {handshake.name = "sitofp0"} : i32 to f32
    %63 = arith.extui %43 {handshake.name = "extui10"} : i32 to i64
    %64 = arith.shli %42, %c1_i64_10 {handshake.name = "shli6"} : i64
    %65 = arith.addi %42, %64 {handshake.name = "addi39"} : i64
    %66 = arith.addi %65, %63 {handshake.name = "addi9"} : i64
    %67 = arith.index_cast %66 {handshake.name = "index_cast6"} : i64 to index
    memref.store %62, %arg3[%67] {handshake.deps = #handshake<deps[{dstAccess : "store0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load8", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store6"} : memref<9xf32>
    %68 = arith.addi %43, %c1_i32_9 {handshake.name = "addi10"} : i32
    %69 = arith.cmpi ult, %68, %c3_i32_8 {handshake.name = "cmpi5"} : i32
    cf.cond_br %69, ^bb8(%68 : i32), ^bb9 {handshake.name = "cond_br4"}
  ^bb9:  // 2 preds: ^bb6, ^bb8
    %c3_i32_11 = arith.constant {handshake.name = "constant21"} 3 : i32
    %c1_i32_12 = arith.constant {handshake.name = "constant22"} 1 : i32
    %c0_i32_13 = arith.constant {handshake.name = "constant23"} 0 : i32
    %70 = arith.addi %14, %c1_i32_12 {handshake.name = "addi11"} : i32
    %71 = arith.cmpi ult, %70, %c3_i32_11 {handshake.name = "cmpi6"} : i32
    cf.cond_br %71, ^bb4(%70 : i32), ^bb10(%c0_i32_13 : i32) {handshake.name = "cond_br5"}
  ^bb10(%72: i32):  // 2 preds: ^bb9, ^bb14
    %c0_i32_14 = arith.constant {handshake.name = "constant24"} 0 : i32
    %73 = arith.extui %72 {handshake.name = "extui11"} : i32 to i64
    %74 = arith.extui %72 {handshake.name = "extui12"} : i32 to i64
    cf.br ^bb11(%c0_i32_14 : i32) {handshake.name = "br4"}
  ^bb11(%75: i32):  // 2 preds: ^bb10, ^bb13
    %c0_i32_15 = arith.constant {handshake.name = "constant25"} 0 : i32
    %c1_i64_16 = arith.constant {handshake.name = "constant26"} 1 : i64
    %76 = arith.extui %75 {handshake.name = "extui13"} : i32 to i64
    %77 = arith.extui %75 {handshake.name = "extui14"} : i32 to i64
    %78 = arith.shli %74, %c1_i64_16 {handshake.name = "shli7"} : i64
    %79 = arith.addi %74, %78 {handshake.name = "addi40"} : i64
    %80 = arith.addi %79, %77 {handshake.name = "addi12"} : i64
    %81 = arith.index_cast %80 {handshake.name = "index_cast7"} : i64 to index
    %82 = memref.load %arg4[%81] {handshake.name = "load7"} : memref<9xf32>
    cf.br ^bb12(%c0_i32_15, %82 : i32, f32) {handshake.name = "br5"}
  ^bb12(%83: i32, %84: f32):  // 2 preds: ^bb11, ^bb12
    %c3_i32_17 = arith.constant {handshake.name = "constant27"} 3 : i32
    %c1_i32_18 = arith.constant {handshake.name = "constant28"} 1 : i32
    %c1_i64_19 = arith.constant {handshake.name = "constant29"} 1 : i64
    %85 = arith.extui %83 {handshake.name = "extui15"} : i32 to i64
    %86 = arith.shli %73, %c1_i64_19 {handshake.name = "shli8"} : i64
    %87 = arith.addi %73, %86 {handshake.name = "addi41"} : i64
    %88 = arith.addi %87, %85 {handshake.name = "addi13"} : i64
    %89 = arith.index_cast %88 {handshake.name = "index_cast8"} : i64 to index
    %90 = memref.load %arg3[%89] {handshake.name = "load8"} : memref<9xf32>
    %91 = arith.extui %83 {handshake.name = "extui16"} : i32 to i64
    %92 = arith.shli %91, %c1_i64_19 {handshake.name = "shli9"} : i64
    %93 = arith.addi %91, %92 {handshake.name = "addi42"} : i64
    %94 = arith.addi %93, %76 {handshake.name = "addi14"} : i64
    %95 = arith.index_cast %94 {handshake.name = "index_cast9"} : i64 to index
    %96 = memref.load %arg0[%95] {handshake.name = "load9"} : memref<9xf32>
    %97 = arith.mulf %90, %96 {handshake.name = "mulf0"} : f32
    %98 = arith.addf %84, %97 {handshake.name = "addf0"} : f32
    %99 = arith.index_cast %80 {handshake.name = "index_cast10"} : i64 to index
    memref.store %98, %arg4[%99] {handshake.deps = #handshake<deps[{dstAccess : "load14", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load18", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store10"} : memref<9xf32>
    %100 = arith.addi %83, %c1_i32_18 {handshake.name = "addi15"} : i32
    %101 = arith.cmpi ult, %100, %c3_i32_17 {handshake.name = "cmpi7"} : i32
    cf.cond_br %101, ^bb12(%100, %98 : i32, f32), ^bb13 {handshake.name = "cond_br6"}
  ^bb13:  // pred: ^bb12
    %c3_i32_20 = arith.constant {handshake.name = "constant30"} 3 : i32
    %c1_i32_21 = arith.constant {handshake.name = "constant31"} 1 : i32
    %102 = arith.addi %75, %c1_i32_21 {handshake.name = "addi16"} : i32
    %103 = arith.cmpi ult, %102, %c3_i32_20 {handshake.name = "cmpi8"} : i32
    cf.cond_br %103, ^bb11(%102 : i32), ^bb14 {handshake.name = "cond_br7"}
  ^bb14:  // pred: ^bb13
    %c3_i32_22 = arith.constant {handshake.name = "constant32"} 3 : i32
    %c1_i32_23 = arith.constant {handshake.name = "constant33"} 1 : i32
    %c0_i32_24 = arith.constant {handshake.name = "constant34"} 0 : i32
    %104 = arith.addi %72, %c1_i32_23 {handshake.name = "addi17"} : i32
    %105 = arith.cmpi ult, %104, %c3_i32_22 {handshake.name = "cmpi9"} : i32
    cf.cond_br %105, ^bb10(%104 : i32), ^bb15(%c0_i32_24 : i32) {handshake.name = "cond_br8"}
  ^bb15(%106: i32):  // 2 preds: ^bb14, ^bb15
    %cst = arith.constant {handshake.name = "constant35"} 1.000000e+00 : f32
    %c3_i32_25 = arith.constant {handshake.name = "constant36"} 3 : i32
    %c1_i32_26 = arith.constant {handshake.name = "constant37"} 1 : i32
    %c0_i32_27 = arith.constant {handshake.name = "constant38"} 0 : i32
    %c1_i64_28 = arith.constant {handshake.name = "constant39"} 1 : i64
    %107 = arith.extui %106 {handshake.name = "extui17"} : i32 to i64
    %108 = arith.extui %106 {handshake.name = "extui18"} : i32 to i64
    %109 = arith.shli %107, %c1_i64_28 {handshake.name = "shli10"} : i64
    %110 = arith.addi %107, %109 {handshake.name = "addi43"} : i64
    %111 = arith.addi %110, %108 {handshake.name = "addi18"} : i64
    %112 = arith.index_cast %111 {handshake.name = "index_cast11"} : i64 to index
    memref.store %cst, %arg1[%112] {handshake.deps = #handshake<deps[{dstAccess : "store20", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store11"} : memref<9xf32>
    %113 = arith.addi %106, %c1_i32_26 {handshake.name = "addi19"} : i32
    %114 = arith.cmpi ult, %113, %c3_i32_25 {handshake.name = "cmpi10"} : i32
    cf.cond_br %114, ^bb15(%113 : i32), ^bb16(%c0_i32_27 : i32) {handshake.name = "cond_br9"}
  ^bb16(%115: i32):  // 2 preds: ^bb15, ^bb26
    %c0_i32_29 = arith.constant {handshake.name = "constant40"} 0 : i32
    cf.br ^bb17(%c0_i32_29 : i32) {handshake.name = "br6"}
  ^bb17(%116: i32):  // 2 preds: ^bb16, ^bb25
    %117 = arith.cmpi ugt, %116, %115 {handshake.name = "cmpi11"} : i32
    cf.cond_br %117, ^bb21(%116 : i32), ^bb18 {handshake.name = "cond_br10"}
  ^bb18:  // pred: ^bb17
    %cst_30 = arith.constant {handshake.name = "constant41"} 0.000000e+00 : f64
    %c0_i32_31 = arith.constant {handshake.name = "constant42"} 0 : i32
    %118 = arith.cmpi ugt, %116, %c0_i32_31 {handshake.name = "cmpi12"} : i32
    cf.cond_br %118, ^bb19(%c0_i32_31, %cst_30 : i32, f64), ^bb20(%cst_30 : f64) {handshake.name = "cond_br11"}
  ^bb19(%119: i32, %120: f64):  // 2 preds: ^bb18, ^bb19
    %c1_i32_32 = arith.constant {handshake.name = "constant43"} 1 : i32
    %c1_i64_33 = arith.constant {handshake.name = "constant44"} 1 : i64
    %121 = arith.extui %116 {handshake.name = "extui19"} : i32 to i64
    %122 = arith.extui %119 {handshake.name = "extui20"} : i32 to i64
    %123 = arith.shli %121, %c1_i64_33 {handshake.name = "shli11"} : i64
    %124 = arith.addi %121, %123 {handshake.name = "addi44"} : i64
    %125 = arith.addi %124, %122 {handshake.name = "addi20"} : i64
    %126 = arith.index_cast %125 {handshake.name = "index_cast12"} : i64 to index
    %127 = memref.load %arg1[%126] {handshake.name = "load12"} : memref<9xf32>
    %128 = arith.extui %119 {handshake.name = "extui21"} : i32 to i64
    %129 = arith.extui %115 {handshake.name = "extui22"} : i32 to i64
    %130 = arith.shli %128, %c1_i64_33 {handshake.name = "shli12"} : i64
    %131 = arith.addi %128, %130 {handshake.name = "addi45"} : i64
    %132 = arith.addi %131, %129 {handshake.name = "addi21"} : i64
    %133 = arith.index_cast %132 {handshake.name = "index_cast13"} : i64 to index
    %134 = memref.load %arg2[%133] {handshake.name = "load13"} : memref<9xf32>
    %135 = arith.mulf %127, %134 {handshake.name = "mulf1"} : f32
    %136 = arith.extf %135 {handshake.name = "extf0"} : f32 to f64
    %137 = arith.addf %120, %136 {handshake.name = "addf1"} : f64
    %138 = arith.addi %119, %c1_i32_32 {handshake.name = "addi22"} : i32
    %139 = arith.cmpi ult, %138, %116 {handshake.name = "cmpi13"} : i32
    cf.cond_br %139, ^bb19(%138, %137 : i32, f64), ^bb20(%137 : f64) {handshake.name = "cond_br12"}
  ^bb20(%140: f64):  // 2 preds: ^bb18, ^bb19
    %c1_i64_34 = arith.constant {handshake.name = "constant45"} 1 : i64
    %141 = arith.extui %116 {handshake.name = "extui23"} : i32 to i64
    %142 = arith.extui %115 {handshake.name = "extui24"} : i32 to i64
    %143 = arith.shli %141, %c1_i64_34 {handshake.name = "shli13"} : i64
    %144 = arith.addi %141, %143 {handshake.name = "addi46"} : i64
    %145 = arith.addi %144, %142 {handshake.name = "addi23"} : i64
    %146 = arith.index_cast %145 {handshake.name = "index_cast14"} : i64 to index
    %147 = memref.load %arg4[%146] {handshake.name = "load14"} : memref<9xf32>
    %148 = arith.extf %147 {handshake.name = "extf1"} : f32 to f64
    %149 = arith.subf %148, %140 {handshake.name = "subf0"} : f64
    %150 = arith.truncf %149 {handshake.name = "truncf0"} : f64 to f32
    %151 = arith.extui %116 {handshake.name = "extui25"} : i32 to i64
    %152 = arith.extui %115 {handshake.name = "extui26"} : i32 to i64
    %153 = arith.shli %151, %c1_i64_34 {handshake.name = "shli14"} : i64
    %154 = arith.addi %151, %153 {handshake.name = "addi47"} : i64
    %155 = arith.addi %154, %152 {handshake.name = "addi24"} : i64
    %156 = arith.index_cast %155 {handshake.name = "index_cast15"} : i64 to index
    memref.store %150, %arg2[%156] {handshake.deps = #handshake<deps[{dstAccess : "load13", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load17", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load19", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store15"} : memref<9xf32>
    cf.br ^bb21(%116 : i32) {handshake.name = "br7"}
  ^bb21(%157: i32):  // 2 preds: ^bb17, ^bb20
    %158 = arith.cmpi ult, %116, %115 {handshake.name = "cmpi14"} : i32
    cf.cond_br %158, ^bb25, ^bb22 {handshake.name = "cond_br13"}
  ^bb22:  // pred: ^bb21
    %cst_35 = arith.constant {handshake.name = "constant46"} 0.000000e+00 : f64
    %c0_i32_36 = arith.constant {handshake.name = "constant47"} 0 : i32
    %159 = arith.cmpi ugt, %115, %c0_i32_36 {handshake.name = "cmpi15"} : i32
    cf.cond_br %159, ^bb23(%c0_i32_36, %cst_35 : i32, f64), ^bb24(%cst_35 : f64) {handshake.name = "cond_br14"}
  ^bb23(%160: i32, %161: f64):  // 2 preds: ^bb22, ^bb23
    %c1_i32_37 = arith.constant {handshake.name = "constant48"} 1 : i32
    %c1_i64_38 = arith.constant {handshake.name = "constant49"} 1 : i64
    %162 = arith.extui %157 {handshake.name = "extui27"} : i32 to i64
    %163 = arith.extui %160 {handshake.name = "extui28"} : i32 to i64
    %164 = arith.shli %162, %c1_i64_38 {handshake.name = "shli15"} : i64
    %165 = arith.addi %162, %164 {handshake.name = "addi48"} : i64
    %166 = arith.addi %165, %163 {handshake.name = "addi25"} : i64
    %167 = arith.index_cast %166 {handshake.name = "index_cast16"} : i64 to index
    %168 = memref.load %arg1[%167] {handshake.name = "load16"} : memref<9xf32>
    %169 = arith.extui %160 {handshake.name = "extui29"} : i32 to i64
    %170 = arith.extui %115 {handshake.name = "extui30"} : i32 to i64
    %171 = arith.shli %169, %c1_i64_38 {handshake.name = "shli16"} : i64
    %172 = arith.addi %169, %171 {handshake.name = "addi49"} : i64
    %173 = arith.addi %172, %170 {handshake.name = "addi26"} : i64
    %174 = arith.index_cast %173 {handshake.name = "index_cast17"} : i64 to index
    %175 = memref.load %arg2[%174] {handshake.name = "load17"} : memref<9xf32>
    %176 = arith.mulf %168, %175 {handshake.name = "mulf2"} : f32
    %177 = arith.extf %176 {handshake.name = "extf2"} : f32 to f64
    %178 = arith.addf %161, %177 {handshake.name = "addf2"} : f64
    %179 = arith.addi %160, %c1_i32_37 {handshake.name = "addi27"} : i32
    %180 = arith.cmpi ult, %179, %115 {handshake.name = "cmpi16"} : i32
    cf.cond_br %180, ^bb23(%179, %178 : i32, f64), ^bb24(%178 : f64) {handshake.name = "cond_br15"}
  ^bb24(%181: f64):  // 2 preds: ^bb22, ^bb23
    %c1_i64_39 = arith.constant {handshake.name = "constant50"} 1 : i64
    %182 = arith.extui %157 {handshake.name = "extui31"} : i32 to i64
    %183 = arith.extui %115 {handshake.name = "extui32"} : i32 to i64
    %184 = arith.shli %182, %c1_i64_39 {handshake.name = "shli17"} : i64
    %185 = arith.addi %182, %184 {handshake.name = "addi50"} : i64
    %186 = arith.addi %185, %183 {handshake.name = "addi28"} : i64
    %187 = arith.index_cast %186 {handshake.name = "index_cast18"} : i64 to index
    %188 = memref.load %arg4[%187] {handshake.name = "load18"} : memref<9xf32>
    %189 = arith.extf %188 {handshake.name = "extf3"} : f32 to f64
    %190 = arith.subf %189, %181 {handshake.name = "subf1"} : f64
    %191 = arith.extui %115 {handshake.name = "extui33"} : i32 to i64
    %192 = arith.extui %115 {handshake.name = "extui34"} : i32 to i64
    %193 = arith.shli %191, %c1_i64_39 {handshake.name = "shli18"} : i64
    %194 = arith.addi %191, %193 {handshake.name = "addi51"} : i64
    %195 = arith.addi %194, %192 {handshake.name = "addi29"} : i64
    %196 = arith.index_cast %195 {handshake.name = "index_cast19"} : i64 to index
    %197 = memref.load %arg2[%196] {handshake.name = "load19"} : memref<9xf32>
    %198 = arith.extf %197 {handshake.name = "extf4"} : f32 to f64
    %199 = arith.divf %190, %198 {handshake.name = "divf0"} : f64
    %200 = arith.truncf %199 {handshake.name = "truncf1"} : f64 to f32
    %201 = arith.extui %157 {handshake.name = "extui35"} : i32 to i64
    %202 = arith.extui %115 {handshake.name = "extui36"} : i32 to i64
    %203 = arith.shli %201, %c1_i64_39 {handshake.name = "shli19"} : i64
    %204 = arith.addi %201, %203 {handshake.name = "addi52"} : i64
    %205 = arith.addi %204, %202 {handshake.name = "addi30"} : i64
    %206 = arith.index_cast %205 {handshake.name = "index_cast20"} : i64 to index
    memref.store %200, %arg1[%206] {handshake.deps = #handshake<deps[{dstAccess : "store11", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load12", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load16", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store20"} : memref<9xf32>
    cf.br ^bb25 {handshake.name = "br8"}
  ^bb25:  // 2 preds: ^bb21, ^bb24
    %c3_i32_40 = arith.constant {handshake.name = "constant51"} 3 : i32
    %c1_i32_41 = arith.constant {handshake.name = "constant52"} 1 : i32
    %207 = arith.addi %157, %c1_i32_41 {handshake.name = "addi31"} : i32
    %208 = arith.cmpi ult, %207, %c3_i32_40 {handshake.name = "cmpi17"} : i32
    cf.cond_br %208, ^bb17(%207 : i32), ^bb26 {handshake.name = "cond_br16"}
  ^bb26:  // pred: ^bb25
    %c3_i32_42 = arith.constant {handshake.name = "constant53"} 3 : i32
    %c1_i32_43 = arith.constant {handshake.name = "constant54"} 1 : i32
    %209 = arith.addi %115, %c1_i32_43 {handshake.name = "addi32"} : i32
    %210 = arith.cmpi ult, %209, %c3_i32_42 {handshake.name = "cmpi18"} : i32
    cf.cond_br %210, ^bb16(%209 : i32), ^bb27 {handshake.name = "cond_br17"}
  ^bb27:  // pred: ^bb26
    return {handshake.name = "return0"}
  }
}

