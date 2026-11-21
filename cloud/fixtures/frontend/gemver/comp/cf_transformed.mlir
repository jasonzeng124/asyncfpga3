module {
  func.func @gemver(%arg0: i32 {handshake.arg_name = "alpha"}, %arg1: i32 {handshake.arg_name = "beta"}, %arg2: memref<30xi32> {handshake.arg_name = "u1"}, %arg3: memref<30xi32> {handshake.arg_name = "v1"}, %arg4: memref<30xi32> {handshake.arg_name = "u2"}, %arg5: memref<30xi32> {handshake.arg_name = "v2"}, %arg6: memref<30xi32> {handshake.arg_name = "y"}, %arg7: memref<30xi32> {handshake.arg_name = "z"}, %arg8: memref<900xi32> {handshake.arg_name = "a"}, %arg9: memref<30xi32> {handshake.arg_name = "w"}, %arg10: memref<30xi32> {handshake.arg_name = "x"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %c0_i32_0 = arith.constant {handshake.name = "constant8"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %3 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    %4 = arith.extui %0 {handshake.name = "extui3"} : i32 to i64
    cf.br ^bb2(%c0_i32_0 : i32) {handshake.name = "br1"}
  ^bb2(%5: i32):  // 2 preds: ^bb1, ^bb2
    %c30_i32 = arith.constant {handshake.name = "constant9"} 30 : i32
    %c1_i32 = arith.constant {handshake.name = "constant10"} 1 : i32
    %c4_i64 = arith.constant {handshake.name = "constant11"} 4 : i64
    %c3_i64 = arith.constant {handshake.name = "constant12"} 3 : i64
    %c2_i64 = arith.constant {handshake.name = "constant13"} 2 : i64
    %c1_i64 = arith.constant {handshake.name = "constant14"} 1 : i64
    %6 = arith.extui %5 {handshake.name = "extui4"} : i32 to i64
    %7 = arith.shli %1, %c1_i64 {handshake.name = "shli0"} : i64
    %8 = arith.shli %1, %c2_i64 {handshake.name = "shli1"} : i64
    %9 = arith.addi %7, %8 {handshake.name = "addi16"} : i64
    %10 = arith.shli %1, %c3_i64 {handshake.name = "shli2"} : i64
    %11 = arith.shli %1, %c4_i64 {handshake.name = "shli3"} : i64
    %12 = arith.addi %10, %11 {handshake.name = "addi17"} : i64
    %13 = arith.addi %9, %12 {handshake.name = "addi18"} : i64
    %14 = arith.addi %13, %6 {handshake.name = "addi0"} : i64
    %15 = arith.index_cast %14 {handshake.name = "index_cast0"} : i64 to index
    %16 = memref.load %arg8[%15] {handshake.name = "load0"} : memref<900xi32>
    %17 = arith.index_cast %2 {handshake.name = "index_cast1"} : i64 to index
    %18 = memref.load %arg2[%17] {handshake.name = "load1"} : memref<30xi32>
    %19 = arith.extui %5 {handshake.name = "extui5"} : i32 to i64
    %20 = arith.index_cast %19 {handshake.name = "index_cast2"} : i64 to index
    %21 = memref.load %arg3[%20] {handshake.name = "load2"} : memref<30xi32>
    %22 = arith.muli %18, %21 {handshake.name = "muli1"} : i32
    %23 = arith.addi %16, %22 {handshake.name = "addi1"} : i32
    %24 = arith.index_cast %3 {handshake.name = "index_cast3"} : i64 to index
    %25 = memref.load %arg4[%24] {handshake.name = "load3"} : memref<30xi32>
    %26 = arith.extui %5 {handshake.name = "extui6"} : i32 to i64
    %27 = arith.index_cast %26 {handshake.name = "index_cast4"} : i64 to index
    %28 = memref.load %arg5[%27] {handshake.name = "load4"} : memref<30xi32>
    %29 = arith.muli %25, %28 {handshake.name = "muli2"} : i32
    %30 = arith.addi %23, %29 {handshake.name = "addi2"} : i32
    %31 = arith.extui %5 {handshake.name = "extui7"} : i32 to i64
    %32 = arith.shli %4, %c1_i64 {handshake.name = "shli4"} : i64
    %33 = arith.shli %4, %c2_i64 {handshake.name = "shli5"} : i64
    %34 = arith.addi %32, %33 {handshake.name = "addi19"} : i64
    %35 = arith.shli %4, %c3_i64 {handshake.name = "shli6"} : i64
    %36 = arith.shli %4, %c4_i64 {handshake.name = "shli7"} : i64
    %37 = arith.addi %35, %36 {handshake.name = "addi20"} : i64
    %38 = arith.addi %34, %37 {handshake.name = "addi21"} : i64
    %39 = arith.addi %38, %31 {handshake.name = "addi3"} : i64
    %40 = arith.index_cast %39 {handshake.name = "index_cast5"} : i64 to index
    memref.store %30, %arg8[%40] {handshake.deps = #handshake<deps[{dstAccess : "load7", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load14", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : memref<900xi32>
    %41 = arith.addi %5, %c1_i32 {handshake.name = "addi4"} : i32
    %42 = arith.cmpi ult, %41, %c30_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %42, ^bb2(%41 : i32), ^bb3 {handshake.name = "cond_br0"}
  ^bb3:  // pred: ^bb2
    %c30_i32_1 = arith.constant {handshake.name = "constant15"} 30 : i32
    %c1_i32_2 = arith.constant {handshake.name = "constant16"} 1 : i32
    %c0_i32_3 = arith.constant {handshake.name = "constant17"} 0 : i32
    %43 = arith.addi %0, %c1_i32_2 {handshake.name = "addi5"} : i32
    %44 = arith.cmpi ult, %43, %c30_i32_1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %44, ^bb1(%43 : i32), ^bb4(%c0_i32_3 : i32) {handshake.name = "cond_br1"}
  ^bb4(%45: i32):  // 2 preds: ^bb3, ^bb6
    %c0_i32_4 = arith.constant {handshake.name = "constant18"} 0 : i32
    %46 = arith.extui %45 {handshake.name = "extui8"} : i32 to i64
    %47 = arith.index_cast %46 {handshake.name = "index_cast6"} : i64 to index
    %48 = memref.load %arg10[%47] {handshake.name = "load6"} : memref<30xi32>
    %49 = arith.extui %45 {handshake.name = "extui9"} : i32 to i64
    cf.br ^bb5(%c0_i32_4, %48 : i32, i32) {handshake.name = "br2"}
  ^bb5(%50: i32, %51: i32):  // 2 preds: ^bb4, ^bb5
    %c30_i32_5 = arith.constant {handshake.name = "constant19"} 30 : i32
    %c1_i32_6 = arith.constant {handshake.name = "constant20"} 1 : i32
    %c4_i64_7 = arith.constant {handshake.name = "constant21"} 4 : i64
    %c3_i64_8 = arith.constant {handshake.name = "constant22"} 3 : i64
    %c2_i64_9 = arith.constant {handshake.name = "constant23"} 2 : i64
    %c1_i64_10 = arith.constant {handshake.name = "constant24"} 1 : i64
    %52 = arith.extui %50 {handshake.name = "extui10"} : i32 to i64
    %53 = arith.shli %52, %c1_i64_10 {handshake.name = "shli8"} : i64
    %54 = arith.shli %52, %c2_i64_9 {handshake.name = "shli9"} : i64
    %55 = arith.addi %53, %54 {handshake.name = "addi22"} : i64
    %56 = arith.shli %52, %c3_i64_8 {handshake.name = "shli10"} : i64
    %57 = arith.shli %52, %c4_i64_7 {handshake.name = "shli11"} : i64
    %58 = arith.addi %56, %57 {handshake.name = "addi23"} : i64
    %59 = arith.addi %55, %58 {handshake.name = "addi24"} : i64
    %60 = arith.addi %59, %49 {handshake.name = "addi6"} : i64
    %61 = arith.index_cast %60 {handshake.name = "index_cast7"} : i64 to index
    %62 = memref.load %arg8[%61] {handshake.name = "load7"} : memref<900xi32>
    %63 = arith.muli %62, %arg1 {handshake.name = "muli5"} : i32
    %64 = arith.extui %50 {handshake.name = "extui11"} : i32 to i64
    %65 = arith.index_cast %64 {handshake.name = "index_cast8"} : i64 to index
    %66 = memref.load %arg6[%65] {handshake.name = "load8"} : memref<30xi32>
    %67 = arith.muli %63, %66 {handshake.name = "muli6"} : i32
    %68 = arith.addi %51, %67 {handshake.name = "addi7"} : i32
    %69 = arith.addi %50, %c1_i32_6 {handshake.name = "addi8"} : i32
    %70 = arith.cmpi ult, %69, %c30_i32_5 {handshake.name = "cmpi2"} : i32
    cf.cond_br %70, ^bb5(%69, %68 : i32, i32), ^bb6(%68 : i32) {handshake.name = "cond_br2"}
  ^bb6(%71: i32):  // pred: ^bb5
    %c30_i32_11 = arith.constant {handshake.name = "constant25"} 30 : i32
    %c1_i32_12 = arith.constant {handshake.name = "constant26"} 1 : i32
    %c0_i32_13 = arith.constant {handshake.name = "constant27"} 0 : i32
    %72 = arith.extui %45 {handshake.name = "extui12"} : i32 to i64
    %73 = arith.index_cast %72 {handshake.name = "index_cast9"} : i64 to index
    memref.store %71, %arg10[%73] {handshake.deps = #handshake<deps[{dstAccess : "load10", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load15", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store12", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store9"} : memref<30xi32>
    %74 = arith.addi %45, %c1_i32_12 {handshake.name = "addi9"} : i32
    %75 = arith.cmpi ult, %74, %c30_i32_11 {handshake.name = "cmpi3"} : i32
    cf.cond_br %75, ^bb4(%74 : i32), ^bb7(%c0_i32_13 : i32) {handshake.name = "cond_br3"}
  ^bb7(%76: i32):  // 2 preds: ^bb6, ^bb7
    %c30_i32_14 = arith.constant {handshake.name = "constant28"} 30 : i32
    %c1_i32_15 = arith.constant {handshake.name = "constant29"} 1 : i32
    %c0_i32_16 = arith.constant {handshake.name = "constant30"} 0 : i32
    %77 = arith.extui %76 {handshake.name = "extui13"} : i32 to i64
    %78 = arith.index_cast %77 {handshake.name = "index_cast10"} : i64 to index
    %79 = memref.load %arg10[%78] {handshake.name = "load10"} : memref<30xi32>
    %80 = arith.extui %76 {handshake.name = "extui14"} : i32 to i64
    %81 = arith.index_cast %80 {handshake.name = "index_cast11"} : i64 to index
    %82 = memref.load %arg7[%81] {handshake.name = "load11"} : memref<30xi32>
    %83 = arith.addi %79, %82 {handshake.name = "addi10"} : i32
    %84 = arith.extui %76 {handshake.name = "extui15"} : i32 to i64
    %85 = arith.index_cast %84 {handshake.name = "index_cast12"} : i64 to index
    memref.store %83, %arg10[%85] {handshake.deps = #handshake<deps[{dstAccess : "store9", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load15", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store12"} : memref<30xi32>
    %86 = arith.addi %76, %c1_i32_15 {handshake.name = "addi11"} : i32
    %87 = arith.cmpi ult, %86, %c30_i32_14 {handshake.name = "cmpi4"} : i32
    cf.cond_br %87, ^bb7(%86 : i32), ^bb8(%c0_i32_16 : i32) {handshake.name = "cond_br4"}
  ^bb8(%88: i32):  // 2 preds: ^bb7, ^bb10
    %c0_i32_17 = arith.constant {handshake.name = "constant31"} 0 : i32
    %89 = arith.extui %88 {handshake.name = "extui16"} : i32 to i64
    %90 = arith.index_cast %89 {handshake.name = "index_cast13"} : i64 to index
    %91 = memref.load %arg9[%90] {handshake.name = "load13"} : memref<30xi32>
    %92 = arith.extui %88 {handshake.name = "extui17"} : i32 to i64
    cf.br ^bb9(%c0_i32_17, %91 : i32, i32) {handshake.name = "br3"}
  ^bb9(%93: i32, %94: i32):  // 2 preds: ^bb8, ^bb9
    %c30_i32_18 = arith.constant {handshake.name = "constant32"} 30 : i32
    %c1_i32_19 = arith.constant {handshake.name = "constant33"} 1 : i32
    %c4_i64_20 = arith.constant {handshake.name = "constant34"} 4 : i64
    %c3_i64_21 = arith.constant {handshake.name = "constant35"} 3 : i64
    %c2_i64_22 = arith.constant {handshake.name = "constant36"} 2 : i64
    %c1_i64_23 = arith.constant {handshake.name = "constant37"} 1 : i64
    %95 = arith.extui %93 {handshake.name = "extui18"} : i32 to i64
    %96 = arith.shli %92, %c1_i64_23 {handshake.name = "shli12"} : i64
    %97 = arith.shli %92, %c2_i64_22 {handshake.name = "shli13"} : i64
    %98 = arith.addi %96, %97 {handshake.name = "addi25"} : i64
    %99 = arith.shli %92, %c3_i64_21 {handshake.name = "shli14"} : i64
    %100 = arith.shli %92, %c4_i64_20 {handshake.name = "shli15"} : i64
    %101 = arith.addi %99, %100 {handshake.name = "addi26"} : i64
    %102 = arith.addi %98, %101 {handshake.name = "addi27"} : i64
    %103 = arith.addi %102, %95 {handshake.name = "addi12"} : i64
    %104 = arith.index_cast %103 {handshake.name = "index_cast14"} : i64 to index
    %105 = memref.load %arg8[%104] {handshake.name = "load14"} : memref<900xi32>
    %106 = arith.muli %105, %arg0 {handshake.name = "muli8"} : i32
    %107 = arith.extui %93 {handshake.name = "extui19"} : i32 to i64
    %108 = arith.index_cast %107 {handshake.name = "index_cast15"} : i64 to index
    %109 = memref.load %arg10[%108] {handshake.name = "load15"} : memref<30xi32>
    %110 = arith.muli %106, %109 {handshake.name = "muli9"} : i32
    %111 = arith.addi %94, %110 {handshake.name = "addi13"} : i32
    %112 = arith.addi %93, %c1_i32_19 {handshake.name = "addi14"} : i32
    %113 = arith.cmpi ult, %112, %c30_i32_18 {handshake.name = "cmpi5"} : i32
    cf.cond_br %113, ^bb9(%112, %111 : i32, i32), ^bb10(%111 : i32) {handshake.name = "cond_br5"}
  ^bb10(%114: i32):  // pred: ^bb9
    %c30_i32_24 = arith.constant {handshake.name = "constant38"} 30 : i32
    %c1_i32_25 = arith.constant {handshake.name = "constant39"} 1 : i32
    %115 = arith.extui %88 {handshake.name = "extui20"} : i32 to i64
    %116 = arith.index_cast %115 {handshake.name = "index_cast16"} : i64 to index
    memref.store %114, %arg9[%116] {handshake.name = "store16"} : memref<30xi32>
    %117 = arith.addi %88, %c1_i32_25 {handshake.name = "addi15"} : i32
    %118 = arith.cmpi ult, %117, %c30_i32_24 {handshake.name = "cmpi6"} : i32
    cf.cond_br %118, ^bb8(%117 : i32), ^bb11 {handshake.name = "cond_br6"}
  ^bb11:  // pred: ^bb10
    return {handshake.name = "return0"}
  }
}

