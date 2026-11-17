module {
  func.func @kernel_3mm_float(%arg0: memref<100xf32> {handshake.arg_name = "A"}, %arg1: memref<100xf32> {handshake.arg_name = "B"}, %arg2: memref<100xf32> {handshake.arg_name = "C"}, %arg3: memref<100xf32> {handshake.arg_name = "D"}, %arg4: memref<100xf32> {handshake.arg_name = "E"}, %arg5: memref<100xf32> {handshake.arg_name = "F"}, %arg6: memref<100xf32> {handshake.arg_name = "G"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb5
    %c0_i32_0 = arith.constant {handshake.name = "constant6"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %3 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    cf.br ^bb2(%c0_i32_0 : i32) {handshake.name = "br1"}
  ^bb2(%4: i32):  // 2 preds: ^bb1, ^bb4
    %c0_i32_1 = arith.constant {handshake.name = "constant7"} 0 : i32
    %c3_i64 = arith.constant {handshake.name = "constant8"} 3 : i64
    %c1_i64 = arith.constant {handshake.name = "constant9"} 1 : i64
    %5 = arith.extui %4 {handshake.name = "extui3"} : i32 to i64
    %6 = arith.shli %1, %c1_i64 {handshake.name = "shli0"} : i64
    %7 = arith.shli %1, %c3_i64 {handshake.name = "shli1"} : i64
    %8 = arith.addi %6, %7 {handshake.name = "addi21"} : i64
    %9 = arith.addi %8, %5 {handshake.name = "addi0"} : i64
    %10 = arith.index_cast %9 {handshake.name = "index_cast0"} : i64 to index
    %11 = memref.load %arg4[%10] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : memref<100xf32>
    %12 = arith.extui %4 {handshake.name = "extui4"} : i32 to i64
    cf.br ^bb3(%11, %c0_i32_1 : f32, i32) {handshake.name = "br2"}
  ^bb3(%13: f32, %14: i32):  // 2 preds: ^bb2, ^bb3
    %c10_i32 = arith.constant {handshake.name = "constant10"} 10 : i32
    %c1_i32 = arith.constant {handshake.name = "constant11"} 1 : i32
    %c3_i64_2 = arith.constant {handshake.name = "constant12"} 3 : i64
    %c1_i64_3 = arith.constant {handshake.name = "constant13"} 1 : i64
    %15 = arith.extui %14 {handshake.name = "extui5"} : i32 to i64
    %16 = arith.shli %2, %c1_i64_3 {handshake.name = "shli2"} : i64
    %17 = arith.shli %2, %c3_i64_2 {handshake.name = "shli3"} : i64
    %18 = arith.addi %16, %17 {handshake.name = "addi22"} : i64
    %19 = arith.addi %18, %15 {handshake.name = "addi1"} : i64
    %20 = arith.index_cast %19 {handshake.name = "index_cast1"} : i64 to index
    %21 = memref.load %arg0[%20] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : memref<100xf32>
    %22 = arith.extui %14 {handshake.name = "extui6"} : i32 to i64
    %23 = arith.shli %22, %c1_i64_3 {handshake.name = "shli4"} : i64
    %24 = arith.shli %22, %c3_i64_2 {handshake.name = "shli5"} : i64
    %25 = arith.addi %23, %24 {handshake.name = "addi23"} : i64
    %26 = arith.addi %25, %12 {handshake.name = "addi2"} : i64
    %27 = arith.index_cast %26 {handshake.name = "index_cast2"} : i64 to index
    %28 = memref.load %arg1[%27] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load2"} : memref<100xf32>
    %29 = arith.mulf %21, %28 {handshake.name = "mulf0"} : f32
    %30 = arith.addf %13, %29 {handshake.name = "addf0"} : f32
    %31 = arith.addi %14, %c1_i32 {handshake.name = "addi3"} : i32
    %32 = arith.cmpi ult, %31, %c10_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %32, ^bb3(%30, %31 : f32, i32), ^bb4(%30 : f32) {handshake.name = "cond_br0"}
  ^bb4(%33: f32):  // pred: ^bb3
    %c10_i32_4 = arith.constant {handshake.name = "constant14"} 10 : i32
    %c1_i32_5 = arith.constant {handshake.name = "constant15"} 1 : i32
    %c3_i64_6 = arith.constant {handshake.name = "constant16"} 3 : i64
    %c1_i64_7 = arith.constant {handshake.name = "constant17"} 1 : i64
    %34 = arith.extui %4 {handshake.name = "extui7"} : i32 to i64
    %35 = arith.shli %3, %c1_i64_7 {handshake.name = "shli6"} : i64
    %36 = arith.shli %3, %c3_i64_6 {handshake.name = "shli7"} : i64
    %37 = arith.addi %35, %36 {handshake.name = "addi24"} : i64
    %38 = arith.addi %37, %34 {handshake.name = "addi4"} : i64
    %39 = arith.index_cast %38 {handshake.name = "index_cast3"} : i64 to index
    memref.store %33, %arg4[%39] {handshake.deps = #handshake<deps[{dstAccess : "load9", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store3"} : memref<100xf32>
    %40 = arith.addi %4, %c1_i32_5 {handshake.name = "addi5"} : i32
    %41 = arith.cmpi ult, %40, %c10_i32_4 {handshake.name = "cmpi1"} : i32
    cf.cond_br %41, ^bb2(%40 : i32), ^bb5 {handshake.name = "cond_br1"}
  ^bb5:  // pred: ^bb4
    %c10_i32_8 = arith.constant {handshake.name = "constant18"} 10 : i32
    %c1_i32_9 = arith.constant {handshake.name = "constant19"} 1 : i32
    %c0_i32_10 = arith.constant {handshake.name = "constant20"} 0 : i32
    %42 = arith.addi %0, %c1_i32_9 {handshake.name = "addi6"} : i32
    %43 = arith.cmpi ult, %42, %c10_i32_8 {handshake.name = "cmpi2"} : i32
    cf.cond_br %43, ^bb1(%42 : i32), ^bb6(%c0_i32_10 : i32) {handshake.name = "cond_br2"}
  ^bb6(%44: i32):  // 2 preds: ^bb5, ^bb10
    %c0_i32_11 = arith.constant {handshake.name = "constant21"} 0 : i32
    %45 = arith.extui %44 {handshake.name = "extui8"} : i32 to i64
    %46 = arith.extui %44 {handshake.name = "extui9"} : i32 to i64
    %47 = arith.extui %44 {handshake.name = "extui10"} : i32 to i64
    cf.br ^bb7(%c0_i32_11 : i32) {handshake.name = "br3"}
  ^bb7(%48: i32):  // 2 preds: ^bb6, ^bb9
    %c0_i32_12 = arith.constant {handshake.name = "constant22"} 0 : i32
    %c3_i64_13 = arith.constant {handshake.name = "constant23"} 3 : i64
    %c1_i64_14 = arith.constant {handshake.name = "constant24"} 1 : i64
    %49 = arith.extui %48 {handshake.name = "extui11"} : i32 to i64
    %50 = arith.shli %45, %c1_i64_14 {handshake.name = "shli8"} : i64
    %51 = arith.shli %45, %c3_i64_13 {handshake.name = "shli9"} : i64
    %52 = arith.addi %50, %51 {handshake.name = "addi25"} : i64
    %53 = arith.addi %52, %49 {handshake.name = "addi7"} : i64
    %54 = arith.index_cast %53 {handshake.name = "index_cast4"} : i64 to index
    %55 = memref.load %arg5[%54] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load4"} : memref<100xf32>
    %56 = arith.extui %48 {handshake.name = "extui12"} : i32 to i64
    cf.br ^bb8(%55, %c0_i32_12 : f32, i32) {handshake.name = "br4"}
  ^bb8(%57: f32, %58: i32):  // 2 preds: ^bb7, ^bb8
    %c10_i32_15 = arith.constant {handshake.name = "constant25"} 10 : i32
    %c1_i32_16 = arith.constant {handshake.name = "constant26"} 1 : i32
    %c3_i64_17 = arith.constant {handshake.name = "constant27"} 3 : i64
    %c1_i64_18 = arith.constant {handshake.name = "constant28"} 1 : i64
    %59 = arith.extui %58 {handshake.name = "extui13"} : i32 to i64
    %60 = arith.shli %46, %c1_i64_18 {handshake.name = "shli10"} : i64
    %61 = arith.shli %46, %c3_i64_17 {handshake.name = "shli11"} : i64
    %62 = arith.addi %60, %61 {handshake.name = "addi26"} : i64
    %63 = arith.addi %62, %59 {handshake.name = "addi8"} : i64
    %64 = arith.index_cast %63 {handshake.name = "index_cast5"} : i64 to index
    %65 = memref.load %arg2[%64] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load5"} : memref<100xf32>
    %66 = arith.extui %58 {handshake.name = "extui14"} : i32 to i64
    %67 = arith.shli %66, %c1_i64_18 {handshake.name = "shli12"} : i64
    %68 = arith.shli %66, %c3_i64_17 {handshake.name = "shli13"} : i64
    %69 = arith.addi %67, %68 {handshake.name = "addi27"} : i64
    %70 = arith.addi %69, %56 {handshake.name = "addi9"} : i64
    %71 = arith.index_cast %70 {handshake.name = "index_cast6"} : i64 to index
    %72 = memref.load %arg3[%71] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load6"} : memref<100xf32>
    %73 = arith.mulf %65, %72 {handshake.name = "mulf1"} : f32
    %74 = arith.addf %57, %73 {handshake.name = "addf1"} : f32
    %75 = arith.addi %58, %c1_i32_16 {handshake.name = "addi10"} : i32
    %76 = arith.cmpi ult, %75, %c10_i32_15 {handshake.name = "cmpi3"} : i32
    cf.cond_br %76, ^bb8(%74, %75 : f32, i32), ^bb9(%74 : f32) {handshake.name = "cond_br3"}
  ^bb9(%77: f32):  // pred: ^bb8
    %c10_i32_19 = arith.constant {handshake.name = "constant29"} 10 : i32
    %c1_i32_20 = arith.constant {handshake.name = "constant30"} 1 : i32
    %c3_i64_21 = arith.constant {handshake.name = "constant31"} 3 : i64
    %c1_i64_22 = arith.constant {handshake.name = "constant32"} 1 : i64
    %78 = arith.extui %48 {handshake.name = "extui15"} : i32 to i64
    %79 = arith.shli %47, %c1_i64_22 {handshake.name = "shli14"} : i64
    %80 = arith.shli %47, %c3_i64_21 {handshake.name = "shli15"} : i64
    %81 = arith.addi %79, %80 {handshake.name = "addi28"} : i64
    %82 = arith.addi %81, %78 {handshake.name = "addi11"} : i64
    %83 = arith.index_cast %82 {handshake.name = "index_cast7"} : i64 to index
    memref.store %77, %arg5[%83] {handshake.deps = #handshake<deps[{dstAccess : "load10", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store7"} : memref<100xf32>
    %84 = arith.addi %48, %c1_i32_20 {handshake.name = "addi12"} : i32
    %85 = arith.cmpi ult, %84, %c10_i32_19 {handshake.name = "cmpi4"} : i32
    cf.cond_br %85, ^bb7(%84 : i32), ^bb10 {handshake.name = "cond_br4"}
  ^bb10:  // pred: ^bb9
    %c10_i32_23 = arith.constant {handshake.name = "constant33"} 10 : i32
    %c1_i32_24 = arith.constant {handshake.name = "constant34"} 1 : i32
    %c0_i32_25 = arith.constant {handshake.name = "constant35"} 0 : i32
    %86 = arith.addi %44, %c1_i32_24 {handshake.name = "addi13"} : i32
    %87 = arith.cmpi ult, %86, %c10_i32_23 {handshake.name = "cmpi5"} : i32
    cf.cond_br %87, ^bb6(%86 : i32), ^bb11(%c0_i32_25 : i32) {handshake.name = "cond_br5"}
  ^bb11(%88: i32):  // 2 preds: ^bb10, ^bb15
    %c0_i32_26 = arith.constant {handshake.name = "constant36"} 0 : i32
    %89 = arith.extui %88 {handshake.name = "extui16"} : i32 to i64
    %90 = arith.extui %88 {handshake.name = "extui17"} : i32 to i64
    %91 = arith.extui %88 {handshake.name = "extui18"} : i32 to i64
    cf.br ^bb12(%c0_i32_26 : i32) {handshake.name = "br5"}
  ^bb12(%92: i32):  // 2 preds: ^bb11, ^bb14
    %c0_i32_27 = arith.constant {handshake.name = "constant37"} 0 : i32
    %c3_i64_28 = arith.constant {handshake.name = "constant38"} 3 : i64
    %c1_i64_29 = arith.constant {handshake.name = "constant39"} 1 : i64
    %93 = arith.extui %92 {handshake.name = "extui19"} : i32 to i64
    %94 = arith.shli %89, %c1_i64_29 {handshake.name = "shli16"} : i64
    %95 = arith.shli %89, %c3_i64_28 {handshake.name = "shli17"} : i64
    %96 = arith.addi %94, %95 {handshake.name = "addi29"} : i64
    %97 = arith.addi %96, %93 {handshake.name = "addi14"} : i64
    %98 = arith.index_cast %97 {handshake.name = "index_cast8"} : i64 to index
    %99 = memref.load %arg6[%98] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load8"} : memref<100xf32>
    %100 = arith.extui %92 {handshake.name = "extui20"} : i32 to i64
    cf.br ^bb13(%99, %c0_i32_27 : f32, i32) {handshake.name = "br6"}
  ^bb13(%101: f32, %102: i32):  // 2 preds: ^bb12, ^bb13
    %c10_i32_30 = arith.constant {handshake.name = "constant40"} 10 : i32
    %c1_i32_31 = arith.constant {handshake.name = "constant41"} 1 : i32
    %c3_i64_32 = arith.constant {handshake.name = "constant42"} 3 : i64
    %c1_i64_33 = arith.constant {handshake.name = "constant43"} 1 : i64
    %103 = arith.extui %102 {handshake.name = "extui21"} : i32 to i64
    %104 = arith.shli %90, %c1_i64_33 {handshake.name = "shli18"} : i64
    %105 = arith.shli %90, %c3_i64_32 {handshake.name = "shli19"} : i64
    %106 = arith.addi %104, %105 {handshake.name = "addi30"} : i64
    %107 = arith.addi %106, %103 {handshake.name = "addi15"} : i64
    %108 = arith.index_cast %107 {handshake.name = "index_cast9"} : i64 to index
    %109 = memref.load %arg4[%108] {handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load9"} : memref<100xf32>
    %110 = arith.extui %102 {handshake.name = "extui22"} : i32 to i64
    %111 = arith.shli %110, %c1_i64_33 {handshake.name = "shli20"} : i64
    %112 = arith.shli %110, %c3_i64_32 {handshake.name = "shli21"} : i64
    %113 = arith.addi %111, %112 {handshake.name = "addi31"} : i64
    %114 = arith.addi %113, %100 {handshake.name = "addi16"} : i64
    %115 = arith.index_cast %114 {handshake.name = "index_cast10"} : i64 to index
    %116 = memref.load %arg5[%115] {handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load10"} : memref<100xf32>
    %117 = arith.mulf %109, %116 {handshake.name = "mulf2"} : f32
    %118 = arith.addf %101, %117 {handshake.name = "addf2"} : f32
    %119 = arith.addi %102, %c1_i32_31 {handshake.name = "addi17"} : i32
    %120 = arith.cmpi ult, %119, %c10_i32_30 {handshake.name = "cmpi6"} : i32
    cf.cond_br %120, ^bb13(%118, %119 : f32, i32), ^bb14(%118 : f32) {handshake.name = "cond_br6"}
  ^bb14(%121: f32):  // pred: ^bb13
    %c10_i32_34 = arith.constant {handshake.name = "constant44"} 10 : i32
    %c1_i32_35 = arith.constant {handshake.name = "constant45"} 1 : i32
    %c3_i64_36 = arith.constant {handshake.name = "constant46"} 3 : i64
    %c1_i64_37 = arith.constant {handshake.name = "constant47"} 1 : i64
    %122 = arith.extui %92 {handshake.name = "extui23"} : i32 to i64
    %123 = arith.shli %91, %c1_i64_37 {handshake.name = "shli22"} : i64
    %124 = arith.shli %91, %c3_i64_36 {handshake.name = "shli23"} : i64
    %125 = arith.addi %123, %124 {handshake.name = "addi32"} : i64
    %126 = arith.addi %125, %122 {handshake.name = "addi18"} : i64
    %127 = arith.index_cast %126 {handshake.name = "index_cast11"} : i64 to index
    memref.store %121, %arg6[%127] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store11"} : memref<100xf32>
    %128 = arith.addi %92, %c1_i32_35 {handshake.name = "addi19"} : i32
    %129 = arith.cmpi ult, %128, %c10_i32_34 {handshake.name = "cmpi7"} : i32
    cf.cond_br %129, ^bb12(%128 : i32), ^bb15 {handshake.name = "cond_br7"}
  ^bb15:  // pred: ^bb14
    %c10_i32_38 = arith.constant {handshake.name = "constant48"} 10 : i32
    %c1_i32_39 = arith.constant {handshake.name = "constant49"} 1 : i32
    %130 = arith.addi %88, %c1_i32_39 {handshake.name = "addi20"} : i32
    %131 = arith.cmpi ult, %130, %c10_i32_38 {handshake.name = "cmpi8"} : i32
    cf.cond_br %131, ^bb11(%130 : i32), ^bb16 {handshake.name = "cond_br8"}
  ^bb16:  // pred: ^bb15
    return {handshake.name = "return0"}
  }
}

