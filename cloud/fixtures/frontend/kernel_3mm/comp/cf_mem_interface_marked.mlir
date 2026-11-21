module {
  func.func @kernel_3mm(%arg0: memref<100xi32> {handshake.arg_name = "A"}, %arg1: memref<100xi32> {handshake.arg_name = "B"}, %arg2: memref<100xi32> {handshake.arg_name = "C"}, %arg3: memref<100xi32> {handshake.arg_name = "D"}, %arg4: memref<100xi32> {handshake.arg_name = "E"}, %arg5: memref<100xi32> {handshake.arg_name = "F"}, %arg6: memref<100xi32> {handshake.arg_name = "G"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb5
    %c0_i32_0 = arith.constant {handshake.name = "constant6"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    cf.br ^bb2(%c0_i32_0 : i32) {handshake.name = "br1"}
  ^bb2(%3: i32):  // 2 preds: ^bb1, ^bb4
    %c0_i32_1 = arith.constant {handshake.name = "constant7"} 0 : i32
    %4 = arith.extui %3 {handshake.name = "extui2"} : i32 to i64
    cf.br ^bb3(%c0_i32_1, %c0_i32_1 : i32, i32) {handshake.name = "br2"}
  ^bb3(%5: i32, %6: i32):  // 2 preds: ^bb2, ^bb3
    %c10_i32 = arith.constant {handshake.name = "constant8"} 10 : i32
    %c1_i32 = arith.constant {handshake.name = "constant9"} 1 : i32
    %c3_i64 = arith.constant {handshake.name = "constant10"} 3 : i64
    %c1_i64 = arith.constant {handshake.name = "constant11"} 1 : i64
    %7 = arith.extui %6 {handshake.name = "extui3"} : i32 to i64
    %8 = arith.shli %1, %c1_i64 {handshake.name = "shli0"} : i64
    %9 = arith.shli %1, %c3_i64 {handshake.name = "shli1"} : i64
    %10 = arith.addi %8, %9 {handshake.name = "addi21"} : i64
    %11 = arith.addi %10, %7 {handshake.name = "addi0"} : i64
    %12 = arith.index_cast %11 {handshake.name = "index_cast0"} : i64 to index
    %13 = memref.load %arg0[%12] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : memref<100xi32>
    %14 = arith.extui %6 {handshake.name = "extui4"} : i32 to i64
    %15 = arith.shli %14, %c1_i64 {handshake.name = "shli2"} : i64
    %16 = arith.shli %14, %c3_i64 {handshake.name = "shli3"} : i64
    %17 = arith.addi %15, %16 {handshake.name = "addi22"} : i64
    %18 = arith.addi %17, %4 {handshake.name = "addi1"} : i64
    %19 = arith.index_cast %18 {handshake.name = "index_cast1"} : i64 to index
    %20 = memref.load %arg1[%19] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : memref<100xi32>
    %21 = arith.muli %13, %20 {handshake.name = "muli2"} : i32
    %22 = arith.addi %5, %21 {handshake.name = "addi2"} : i32
    %23 = arith.addi %6, %c1_i32 {handshake.name = "addi3"} : i32
    %24 = arith.cmpi ult, %23, %c10_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %24, ^bb3(%22, %23 : i32, i32), ^bb4(%22 : i32) {handshake.name = "cond_br0"}
  ^bb4(%25: i32):  // pred: ^bb3
    %c10_i32_2 = arith.constant {handshake.name = "constant12"} 10 : i32
    %c1_i32_3 = arith.constant {handshake.name = "constant13"} 1 : i32
    %c3_i64_4 = arith.constant {handshake.name = "constant14"} 3 : i64
    %c1_i64_5 = arith.constant {handshake.name = "constant15"} 1 : i64
    %26 = arith.extui %3 {handshake.name = "extui5"} : i32 to i64
    %27 = arith.shli %2, %c1_i64_5 {handshake.name = "shli4"} : i64
    %28 = arith.shli %2, %c3_i64_4 {handshake.name = "shli5"} : i64
    %29 = arith.addi %27, %28 {handshake.name = "addi23"} : i64
    %30 = arith.addi %29, %26 {handshake.name = "addi4"} : i64
    %31 = arith.index_cast %30 {handshake.name = "index_cast2"} : i64 to index
    memref.store %25, %arg4[%31] {handshake.deps = #handshake<deps[{dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store2"} : memref<100xi32>
    %32 = arith.addi %3, %c1_i32_3 {handshake.name = "addi5"} : i32
    %33 = arith.cmpi ult, %32, %c10_i32_2 {handshake.name = "cmpi1"} : i32
    cf.cond_br %33, ^bb2(%32 : i32), ^bb5 {handshake.name = "cond_br1"}
  ^bb5:  // pred: ^bb4
    %c10_i32_6 = arith.constant {handshake.name = "constant16"} 10 : i32
    %c1_i32_7 = arith.constant {handshake.name = "constant17"} 1 : i32
    %c0_i32_8 = arith.constant {handshake.name = "constant18"} 0 : i32
    %34 = arith.addi %0, %c1_i32_7 {handshake.name = "addi6"} : i32
    %35 = arith.cmpi ult, %34, %c10_i32_6 {handshake.name = "cmpi2"} : i32
    cf.cond_br %35, ^bb1(%34 : i32), ^bb6(%c0_i32_8 : i32) {handshake.name = "cond_br2"}
  ^bb6(%36: i32):  // 2 preds: ^bb5, ^bb10
    %c0_i32_9 = arith.constant {handshake.name = "constant19"} 0 : i32
    %37 = arith.extui %36 {handshake.name = "extui6"} : i32 to i64
    %38 = arith.extui %36 {handshake.name = "extui7"} : i32 to i64
    cf.br ^bb7(%c0_i32_9 : i32) {handshake.name = "br3"}
  ^bb7(%39: i32):  // 2 preds: ^bb6, ^bb9
    %c0_i32_10 = arith.constant {handshake.name = "constant20"} 0 : i32
    %40 = arith.extui %39 {handshake.name = "extui8"} : i32 to i64
    cf.br ^bb8(%c0_i32_10, %c0_i32_10 : i32, i32) {handshake.name = "br4"}
  ^bb8(%41: i32, %42: i32):  // 2 preds: ^bb7, ^bb8
    %c10_i32_11 = arith.constant {handshake.name = "constant21"} 10 : i32
    %c1_i32_12 = arith.constant {handshake.name = "constant22"} 1 : i32
    %c3_i64_13 = arith.constant {handshake.name = "constant23"} 3 : i64
    %c1_i64_14 = arith.constant {handshake.name = "constant24"} 1 : i64
    %43 = arith.extui %41 {handshake.name = "extui9"} : i32 to i64
    %44 = arith.shli %37, %c1_i64_14 {handshake.name = "shli6"} : i64
    %45 = arith.shli %37, %c3_i64_13 {handshake.name = "shli7"} : i64
    %46 = arith.addi %44, %45 {handshake.name = "addi24"} : i64
    %47 = arith.addi %46, %43 {handshake.name = "addi7"} : i64
    %48 = arith.index_cast %47 {handshake.name = "index_cast3"} : i64 to index
    %49 = memref.load %arg2[%48] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load3"} : memref<100xi32>
    %50 = arith.extui %41 {handshake.name = "extui10"} : i32 to i64
    %51 = arith.shli %50, %c1_i64_14 {handshake.name = "shli8"} : i64
    %52 = arith.shli %50, %c3_i64_13 {handshake.name = "shli9"} : i64
    %53 = arith.addi %51, %52 {handshake.name = "addi25"} : i64
    %54 = arith.addi %53, %40 {handshake.name = "addi8"} : i64
    %55 = arith.index_cast %54 {handshake.name = "index_cast4"} : i64 to index
    %56 = memref.load %arg3[%55] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load4"} : memref<100xi32>
    %57 = arith.muli %49, %56 {handshake.name = "muli6"} : i32
    %58 = arith.addi %42, %57 {handshake.name = "addi9"} : i32
    %59 = arith.addi %41, %c1_i32_12 {handshake.name = "addi10"} : i32
    %60 = arith.cmpi ult, %59, %c10_i32_11 {handshake.name = "cmpi3"} : i32
    cf.cond_br %60, ^bb8(%59, %58 : i32, i32), ^bb9(%58 : i32) {handshake.name = "cond_br3"}
  ^bb9(%61: i32):  // pred: ^bb8
    %c10_i32_15 = arith.constant {handshake.name = "constant25"} 10 : i32
    %c1_i32_16 = arith.constant {handshake.name = "constant26"} 1 : i32
    %c3_i64_17 = arith.constant {handshake.name = "constant27"} 3 : i64
    %c1_i64_18 = arith.constant {handshake.name = "constant28"} 1 : i64
    %62 = arith.extui %39 {handshake.name = "extui11"} : i32 to i64
    %63 = arith.shli %38, %c1_i64_18 {handshake.name = "shli10"} : i64
    %64 = arith.shli %38, %c3_i64_17 {handshake.name = "shli11"} : i64
    %65 = arith.addi %63, %64 {handshake.name = "addi26"} : i64
    %66 = arith.addi %65, %62 {handshake.name = "addi11"} : i64
    %67 = arith.index_cast %66 {handshake.name = "index_cast5"} : i64 to index
    memref.store %61, %arg5[%67] {handshake.deps = #handshake<deps[{dstAccess : "load7", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store5"} : memref<100xi32>
    %68 = arith.addi %39, %c1_i32_16 {handshake.name = "addi12"} : i32
    %69 = arith.cmpi ult, %68, %c10_i32_15 {handshake.name = "cmpi4"} : i32
    cf.cond_br %69, ^bb7(%68 : i32), ^bb10 {handshake.name = "cond_br4"}
  ^bb10:  // pred: ^bb9
    %c10_i32_19 = arith.constant {handshake.name = "constant29"} 10 : i32
    %c1_i32_20 = arith.constant {handshake.name = "constant30"} 1 : i32
    %c0_i32_21 = arith.constant {handshake.name = "constant31"} 0 : i32
    %70 = arith.addi %36, %c1_i32_20 {handshake.name = "addi13"} : i32
    %71 = arith.cmpi ult, %70, %c10_i32_19 {handshake.name = "cmpi5"} : i32
    cf.cond_br %71, ^bb6(%70 : i32), ^bb11(%c0_i32_21 : i32) {handshake.name = "cond_br5"}
  ^bb11(%72: i32):  // 2 preds: ^bb10, ^bb15
    %c0_i32_22 = arith.constant {handshake.name = "constant32"} 0 : i32
    %73 = arith.extui %72 {handshake.name = "extui12"} : i32 to i64
    %74 = arith.extui %72 {handshake.name = "extui13"} : i32 to i64
    cf.br ^bb12(%c0_i32_22 : i32) {handshake.name = "br5"}
  ^bb12(%75: i32):  // 2 preds: ^bb11, ^bb14
    %c0_i32_23 = arith.constant {handshake.name = "constant33"} 0 : i32
    %76 = arith.extui %75 {handshake.name = "extui14"} : i32 to i64
    cf.br ^bb13(%c0_i32_23, %c0_i32_23 : i32, i32) {handshake.name = "br6"}
  ^bb13(%77: i32, %78: i32):  // 2 preds: ^bb12, ^bb13
    %c10_i32_24 = arith.constant {handshake.name = "constant34"} 10 : i32
    %c1_i32_25 = arith.constant {handshake.name = "constant35"} 1 : i32
    %c3_i64_26 = arith.constant {handshake.name = "constant36"} 3 : i64
    %c1_i64_27 = arith.constant {handshake.name = "constant37"} 1 : i64
    %79 = arith.extui %77 {handshake.name = "extui15"} : i32 to i64
    %80 = arith.shli %73, %c1_i64_27 {handshake.name = "shli12"} : i64
    %81 = arith.shli %73, %c3_i64_26 {handshake.name = "shli13"} : i64
    %82 = arith.addi %80, %81 {handshake.name = "addi27"} : i64
    %83 = arith.addi %82, %79 {handshake.name = "addi14"} : i64
    %84 = arith.index_cast %83 {handshake.name = "index_cast6"} : i64 to index
    %85 = memref.load %arg4[%84] {handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load6"} : memref<100xi32>
    %86 = arith.extui %77 {handshake.name = "extui16"} : i32 to i64
    %87 = arith.shli %86, %c1_i64_27 {handshake.name = "shli14"} : i64
    %88 = arith.shli %86, %c3_i64_26 {handshake.name = "shli15"} : i64
    %89 = arith.addi %87, %88 {handshake.name = "addi28"} : i64
    %90 = arith.addi %89, %76 {handshake.name = "addi15"} : i64
    %91 = arith.index_cast %90 {handshake.name = "index_cast7"} : i64 to index
    %92 = memref.load %arg5[%91] {handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load7"} : memref<100xi32>
    %93 = arith.muli %85, %92 {handshake.name = "muli10"} : i32
    %94 = arith.addi %78, %93 {handshake.name = "addi16"} : i32
    %95 = arith.addi %77, %c1_i32_25 {handshake.name = "addi17"} : i32
    %96 = arith.cmpi ult, %95, %c10_i32_24 {handshake.name = "cmpi6"} : i32
    cf.cond_br %96, ^bb13(%95, %94 : i32, i32), ^bb14(%94 : i32) {handshake.name = "cond_br6"}
  ^bb14(%97: i32):  // pred: ^bb13
    %c10_i32_28 = arith.constant {handshake.name = "constant38"} 10 : i32
    %c1_i32_29 = arith.constant {handshake.name = "constant39"} 1 : i32
    %c3_i64_30 = arith.constant {handshake.name = "constant40"} 3 : i64
    %c1_i64_31 = arith.constant {handshake.name = "constant41"} 1 : i64
    %98 = arith.extui %75 {handshake.name = "extui17"} : i32 to i64
    %99 = arith.shli %74, %c1_i64_31 {handshake.name = "shli16"} : i64
    %100 = arith.shli %74, %c3_i64_30 {handshake.name = "shli17"} : i64
    %101 = arith.addi %99, %100 {handshake.name = "addi29"} : i64
    %102 = arith.addi %101, %98 {handshake.name = "addi18"} : i64
    %103 = arith.index_cast %102 {handshake.name = "index_cast8"} : i64 to index
    memref.store %97, %arg6[%103] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store8"} : memref<100xi32>
    %104 = arith.addi %75, %c1_i32_29 {handshake.name = "addi19"} : i32
    %105 = arith.cmpi ult, %104, %c10_i32_28 {handshake.name = "cmpi7"} : i32
    cf.cond_br %105, ^bb12(%104 : i32), ^bb15 {handshake.name = "cond_br7"}
  ^bb15:  // pred: ^bb14
    %c10_i32_32 = arith.constant {handshake.name = "constant42"} 10 : i32
    %c1_i32_33 = arith.constant {handshake.name = "constant43"} 1 : i32
    %106 = arith.addi %72, %c1_i32_33 {handshake.name = "addi20"} : i32
    %107 = arith.cmpi ult, %106, %c10_i32_32 {handshake.name = "cmpi8"} : i32
    cf.cond_br %107, ^bb11(%106 : i32), ^bb16 {handshake.name = "cond_br8"}
  ^bb16:  // pred: ^bb15
    return {handshake.name = "return0"}
  }
}

