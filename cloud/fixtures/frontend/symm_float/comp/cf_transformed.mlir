module {
  func.func @symm_float(%arg0: memref<900xf32> {handshake.arg_name = "A"}, %arg1: memref<900xf32> {handshake.arg_name = "B"}, %arg2: memref<900xf32> {handshake.arg_name = "C"}, %arg3: f32 {handshake.arg_name = "alpha"}, %arg4: f32 {handshake.arg_name = "beta"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb5
    %c0_i32_0 = arith.constant {handshake.name = "constant11"} 0 : i32
    %c4_i64 = arith.constant {handshake.name = "constant12"} 4 : i64
    %c3_i64 = arith.constant {handshake.name = "constant13"} 3 : i64
    %c2_i64 = arith.constant {handshake.name = "constant14"} 2 : i64
    %c1_i64 = arith.constant {handshake.name = "constant15"} 1 : i64
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %3 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    %4 = arith.shli %2, %c1_i64 {handshake.name = "shli0"} : i64
    %5 = arith.shli %2, %c2_i64 {handshake.name = "shli1"} : i64
    %6 = arith.addi %4, %5 {handshake.name = "addi13"} : i64
    %7 = arith.shli %2, %c3_i64 {handshake.name = "shli2"} : i64
    %8 = arith.shli %2, %c4_i64 {handshake.name = "shli3"} : i64
    %9 = arith.addi %7, %8 {handshake.name = "addi14"} : i64
    %10 = arith.addi %6, %9 {handshake.name = "addi15"} : i64
    %11 = arith.addi %10, %3 {handshake.name = "addi0"} : i64
    %12 = arith.extui %0 {handshake.name = "extui3"} : i32 to i64
    %13 = arith.extui %0 {handshake.name = "extui4"} : i32 to i64
    cf.br ^bb2(%c0_i32_0 : i32) {handshake.name = "br1"}
  ^bb2(%14: i32):  // 2 preds: ^bb1, ^bb4
    %cst = arith.constant {handshake.name = "constant16"} 0.000000e+00 : f32
    %c-1_i32 = arith.constant {handshake.name = "constant17"} -1 : i32
    %c0_i32_1 = arith.constant {handshake.name = "constant18"} 0 : i32
    %15 = arith.addi %14, %c-1_i32 {handshake.name = "addi1"} : i32
    %16 = arith.cmpi sgt, %15, %c0_i32_1 {handshake.name = "cmpi0"} : i32
    cf.cond_br %16, ^bb3(%cst, %c0_i32_1 : f32, i32), ^bb4(%cst : f32) {handshake.name = "cond_br0"}
  ^bb3(%17: f32, %18: i32):  // 2 preds: ^bb2, ^bb3
    %c1_i32 = arith.constant {handshake.name = "constant19"} 1 : i32
    %c4_i64_2 = arith.constant {handshake.name = "constant20"} 4 : i64
    %c3_i64_3 = arith.constant {handshake.name = "constant21"} 3 : i64
    %c2_i64_4 = arith.constant {handshake.name = "constant22"} 2 : i64
    %c1_i64_5 = arith.constant {handshake.name = "constant23"} 1 : i64
    %19 = arith.extui %18 {handshake.name = "extui5"} : i32 to i64
    %20 = arith.extui %0 {handshake.name = "extui6"} : i32 to i64
    %21 = arith.shli %19, %c1_i64_5 {handshake.name = "shli4"} : i64
    %22 = arith.shli %19, %c2_i64_4 {handshake.name = "shli5"} : i64
    %23 = arith.addi %21, %22 {handshake.name = "addi16"} : i64
    %24 = arith.shli %19, %c3_i64_3 {handshake.name = "shli6"} : i64
    %25 = arith.shli %19, %c4_i64_2 {handshake.name = "shli7"} : i64
    %26 = arith.addi %24, %25 {handshake.name = "addi17"} : i64
    %27 = arith.addi %23, %26 {handshake.name = "addi18"} : i64
    %28 = arith.addi %27, %20 {handshake.name = "addi2"} : i64
    %29 = arith.index_cast %28 {handshake.name = "index_cast0"} : i64 to index
    %30 = memref.load %arg0[%29] {handshake.name = "load0"} : memref<900xf32>
    %31 = arith.mulf %30, %arg3 {handshake.name = "mulf0"} : f32
    %32 = arith.extui %0 {handshake.name = "extui7"} : i32 to i64
    %33 = arith.extui %14 {handshake.name = "extui8"} : i32 to i64
    %34 = arith.shli %32, %c1_i64_5 {handshake.name = "shli8"} : i64
    %35 = arith.shli %32, %c2_i64_4 {handshake.name = "shli9"} : i64
    %36 = arith.addi %34, %35 {handshake.name = "addi19"} : i64
    %37 = arith.shli %32, %c3_i64_3 {handshake.name = "shli10"} : i64
    %38 = arith.shli %32, %c4_i64_2 {handshake.name = "shli11"} : i64
    %39 = arith.addi %37, %38 {handshake.name = "addi20"} : i64
    %40 = arith.addi %36, %39 {handshake.name = "addi21"} : i64
    %41 = arith.addi %40, %33 {handshake.name = "addi3"} : i64
    %42 = arith.index_cast %41 {handshake.name = "index_cast1"} : i64 to index
    %43 = memref.load %arg1[%42] {handshake.name = "load1"} : memref<900xf32>
    %44 = arith.mulf %31, %43 {handshake.name = "mulf1"} : f32
    %45 = arith.extui %18 {handshake.name = "extui9"} : i32 to i64
    %46 = arith.extui %14 {handshake.name = "extui10"} : i32 to i64
    %47 = arith.shli %45, %c1_i64_5 {handshake.name = "shli12"} : i64
    %48 = arith.shli %45, %c2_i64_4 {handshake.name = "shli13"} : i64
    %49 = arith.addi %47, %48 {handshake.name = "addi22"} : i64
    %50 = arith.shli %45, %c3_i64_3 {handshake.name = "shli14"} : i64
    %51 = arith.shli %45, %c4_i64_2 {handshake.name = "shli15"} : i64
    %52 = arith.addi %50, %51 {handshake.name = "addi23"} : i64
    %53 = arith.addi %49, %52 {handshake.name = "addi24"} : i64
    %54 = arith.addi %53, %46 {handshake.name = "addi4"} : i64
    %55 = arith.index_cast %54 {handshake.name = "index_cast2"} : i64 to index
    %56 = memref.load %arg2[%55] {handshake.name = "load2"} : memref<900xf32>
    %57 = arith.addf %56, %44 {handshake.name = "addf0"} : f32
    %58 = arith.index_cast %54 {handshake.name = "index_cast3"} : i64 to index
    memref.store %57, %arg2[%58] {handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store9", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : memref<900xf32>
    %59 = arith.extui %18 {handshake.name = "extui11"} : i32 to i64
    %60 = arith.extui %14 {handshake.name = "extui12"} : i32 to i64
    %61 = arith.shli %59, %c1_i64_5 {handshake.name = "shli16"} : i64
    %62 = arith.shli %59, %c2_i64_4 {handshake.name = "shli17"} : i64
    %63 = arith.addi %61, %62 {handshake.name = "addi25"} : i64
    %64 = arith.shli %59, %c3_i64_3 {handshake.name = "shli18"} : i64
    %65 = arith.shli %59, %c4_i64_2 {handshake.name = "shli19"} : i64
    %66 = arith.addi %64, %65 {handshake.name = "addi26"} : i64
    %67 = arith.addi %63, %66 {handshake.name = "addi27"} : i64
    %68 = arith.addi %67, %60 {handshake.name = "addi5"} : i64
    %69 = arith.index_cast %68 {handshake.name = "index_cast4"} : i64 to index
    %70 = memref.load %arg1[%69] {handshake.name = "load4"} : memref<900xf32>
    %71 = arith.extui %18 {handshake.name = "extui13"} : i32 to i64
    %72 = arith.extui %0 {handshake.name = "extui14"} : i32 to i64
    %73 = arith.shli %71, %c1_i64_5 {handshake.name = "shli20"} : i64
    %74 = arith.shli %71, %c2_i64_4 {handshake.name = "shli21"} : i64
    %75 = arith.addi %73, %74 {handshake.name = "addi28"} : i64
    %76 = arith.shli %71, %c3_i64_3 {handshake.name = "shli22"} : i64
    %77 = arith.shli %71, %c4_i64_2 {handshake.name = "shli23"} : i64
    %78 = arith.addi %76, %77 {handshake.name = "addi29"} : i64
    %79 = arith.addi %75, %78 {handshake.name = "addi30"} : i64
    %80 = arith.addi %79, %72 {handshake.name = "addi6"} : i64
    %81 = arith.index_cast %80 {handshake.name = "index_cast5"} : i64 to index
    %82 = memref.load %arg0[%81] {handshake.name = "load5"} : memref<900xf32>
    %83 = arith.mulf %70, %82 {handshake.name = "mulf2"} : f32
    %84 = arith.addf %17, %83 {handshake.name = "addf1"} : f32
    %85 = arith.addi %18, %c1_i32 {handshake.name = "addi7"} : i32
    %86 = arith.cmpi slt, %85, %15 {handshake.name = "cmpi1"} : i32
    cf.cond_br %86, ^bb3(%84, %85 : f32, i32), ^bb4(%84 : f32) {handshake.name = "cond_br1"}
  ^bb4(%87: f32):  // 2 preds: ^bb2, ^bb3
    %c30_i32 = arith.constant {handshake.name = "constant24"} 30 : i32
    %c1_i32_6 = arith.constant {handshake.name = "constant25"} 1 : i32
    %c4_i64_7 = arith.constant {handshake.name = "constant26"} 4 : i64
    %c3_i64_8 = arith.constant {handshake.name = "constant27"} 3 : i64
    %c2_i64_9 = arith.constant {handshake.name = "constant28"} 2 : i64
    %c1_i64_10 = arith.constant {handshake.name = "constant29"} 1 : i64
    %88 = arith.extui %14 {handshake.name = "extui15"} : i32 to i64
    %89 = arith.shli %1, %c1_i64_10 {handshake.name = "shli24"} : i64
    %90 = arith.shli %1, %c2_i64_9 {handshake.name = "shli25"} : i64
    %91 = arith.addi %89, %90 {handshake.name = "addi31"} : i64
    %92 = arith.shli %1, %c3_i64_8 {handshake.name = "shli26"} : i64
    %93 = arith.shli %1, %c4_i64_7 {handshake.name = "shli27"} : i64
    %94 = arith.addi %92, %93 {handshake.name = "addi32"} : i64
    %95 = arith.addi %91, %94 {handshake.name = "addi33"} : i64
    %96 = arith.addi %95, %88 {handshake.name = "addi8"} : i64
    %97 = arith.index_cast %96 {handshake.name = "index_cast6"} : i64 to index
    %98 = memref.load %arg2[%97] {handshake.name = "load6"} : memref<900xf32>
    %99 = arith.mulf %98, %arg4 {handshake.name = "mulf3"} : f32
    %100 = arith.index_cast %11 {handshake.name = "index_cast7"} : i64 to index
    %101 = memref.load %arg0[%100] {handshake.name = "load7"} : memref<900xf32>
    %102 = arith.mulf %101, %arg3 {handshake.name = "mulf4"} : f32
    %103 = arith.extui %14 {handshake.name = "extui16"} : i32 to i64
    %104 = arith.shli %12, %c1_i64_10 {handshake.name = "shli28"} : i64
    %105 = arith.shli %12, %c2_i64_9 {handshake.name = "shli29"} : i64
    %106 = arith.addi %104, %105 {handshake.name = "addi34"} : i64
    %107 = arith.shli %12, %c3_i64_8 {handshake.name = "shli30"} : i64
    %108 = arith.shli %12, %c4_i64_7 {handshake.name = "shli31"} : i64
    %109 = arith.addi %107, %108 {handshake.name = "addi35"} : i64
    %110 = arith.addi %106, %109 {handshake.name = "addi36"} : i64
    %111 = arith.addi %110, %103 {handshake.name = "addi9"} : i64
    %112 = arith.index_cast %111 {handshake.name = "index_cast8"} : i64 to index
    %113 = memref.load %arg1[%112] {handshake.name = "load8"} : memref<900xf32>
    %114 = arith.mulf %102, %113 {handshake.name = "mulf5"} : f32
    %115 = arith.addf %99, %114 {handshake.name = "addf2"} : f32
    %116 = arith.mulf %87, %arg3 {handshake.name = "mulf6"} : f32
    %117 = arith.addf %115, %116 {handshake.name = "addf3"} : f32
    %118 = arith.extui %14 {handshake.name = "extui17"} : i32 to i64
    %119 = arith.shli %13, %c1_i64_10 {handshake.name = "shli32"} : i64
    %120 = arith.shli %13, %c2_i64_9 {handshake.name = "shli33"} : i64
    %121 = arith.addi %119, %120 {handshake.name = "addi37"} : i64
    %122 = arith.shli %13, %c3_i64_8 {handshake.name = "shli34"} : i64
    %123 = arith.shli %13, %c4_i64_7 {handshake.name = "shli35"} : i64
    %124 = arith.addi %122, %123 {handshake.name = "addi38"} : i64
    %125 = arith.addi %121, %124 {handshake.name = "addi39"} : i64
    %126 = arith.addi %125, %118 {handshake.name = "addi10"} : i64
    %127 = arith.index_cast %126 {handshake.name = "index_cast9"} : i64 to index
    memref.store %117, %arg2[%127] {handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store9"} : memref<900xf32>
    %128 = arith.addi %14, %c1_i32_6 {handshake.name = "addi11"} : i32
    %129 = arith.cmpi ult, %128, %c30_i32 {handshake.name = "cmpi2"} : i32
    cf.cond_br %129, ^bb2(%128 : i32), ^bb5 {handshake.name = "cond_br2"}
  ^bb5:  // pred: ^bb4
    %c10_i32 = arith.constant {handshake.name = "constant30"} 10 : i32
    %c1_i32_11 = arith.constant {handshake.name = "constant31"} 1 : i32
    %130 = arith.addi %0, %c1_i32_11 {handshake.name = "addi12"} : i32
    %131 = arith.cmpi ult, %130, %c10_i32 {handshake.name = "cmpi3"} : i32
    cf.cond_br %131, ^bb1(%130 : i32), ^bb6 {handshake.name = "cond_br3"}
  ^bb6:  // pred: ^bb5
    return {handshake.name = "return0"}
  }
}

