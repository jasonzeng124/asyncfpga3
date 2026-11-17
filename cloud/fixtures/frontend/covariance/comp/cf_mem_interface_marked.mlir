module {
  func.func @covariance(%arg0: memref<900xi32> {handshake.arg_name = "data"}, %arg1: memref<900xi32> {handshake.arg_name = "symmat"}, %arg2: memref<30xi32> {handshake.arg_name = "mean"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %c0_i32_0 = arith.constant {handshake.name = "constant8"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    cf.br ^bb2(%c0_i32_0, %c0_i32_0 : i32, i32) {handshake.name = "br1"}
  ^bb2(%2: i32, %3: i32):  // 2 preds: ^bb1, ^bb2
    %c30_i32 = arith.constant {handshake.name = "constant9"} 30 : i32
    %c1_i32 = arith.constant {handshake.name = "constant10"} 1 : i32
    %c4_i64 = arith.constant {handshake.name = "constant11"} 4 : i64
    %c3_i64 = arith.constant {handshake.name = "constant12"} 3 : i64
    %c2_i64 = arith.constant {handshake.name = "constant13"} 2 : i64
    %c1_i64 = arith.constant {handshake.name = "constant14"} 1 : i64
    %4 = arith.extui %3 {handshake.name = "extui1"} : i32 to i64
    %5 = arith.shli %4, %c1_i64 {handshake.name = "shli0"} : i64
    %6 = arith.shli %4, %c2_i64 {handshake.name = "shli1"} : i64
    %7 = arith.addi %5, %6 {handshake.name = "addi15"} : i64
    %8 = arith.shli %4, %c3_i64 {handshake.name = "shli2"} : i64
    %9 = arith.shli %4, %c4_i64 {handshake.name = "shli3"} : i64
    %10 = arith.addi %8, %9 {handshake.name = "addi16"} : i64
    %11 = arith.addi %7, %10 {handshake.name = "addi17"} : i64
    %12 = arith.addi %11, %1 {handshake.name = "addi0"} : i64
    %13 = arith.index_cast %12 {handshake.name = "index_cast0"} : i64 to index
    %14 = memref.load %arg0[%13] {handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load0"} : memref<900xi32>
    %15 = arith.addi %2, %14 {handshake.name = "addi1"} : i32
    %16 = arith.addi %3, %c1_i32 {handshake.name = "addi2"} : i32
    %17 = arith.cmpi ult, %16, %c30_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %17, ^bb2(%15, %16 : i32, i32), ^bb3(%15 : i32) {handshake.name = "cond_br0"}
  ^bb3(%18: i32):  // pred: ^bb2
    %c30_i32_1 = arith.constant {handshake.name = "constant15"} 30 : i32
    %c1_i32_2 = arith.constant {handshake.name = "constant16"} 1 : i32
    %c0_i32_3 = arith.constant {handshake.name = "constant17"} 0 : i32
    %19 = arith.divsi %18, %c30_i32_1 {handshake.name = "divsi0"} : i32
    %20 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    %21 = arith.index_cast %20 {handshake.name = "index_cast1"} : i64 to index
    memref.store %19, %arg2[%21] {handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store1"} : memref<30xi32>
    %22 = arith.addi %0, %c1_i32_2 {handshake.name = "addi3"} : i32
    %23 = arith.cmpi ult, %22, %c30_i32_1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %23, ^bb1(%22 : i32), ^bb4(%c0_i32_3 : i32) {handshake.name = "cond_br1"}
  ^bb4(%24: i32):  // 2 preds: ^bb3, ^bb6
    %c0_i32_4 = arith.constant {handshake.name = "constant18"} 0 : i32
    %25 = arith.extui %24 {handshake.name = "extui3"} : i32 to i64
    cf.br ^bb5(%c0_i32_4 : i32) {handshake.name = "br2"}
  ^bb5(%26: i32):  // 2 preds: ^bb4, ^bb5
    %c30_i32_5 = arith.constant {handshake.name = "constant19"} 30 : i32
    %c1_i32_6 = arith.constant {handshake.name = "constant20"} 1 : i32
    %c4_i64_7 = arith.constant {handshake.name = "constant21"} 4 : i64
    %c3_i64_8 = arith.constant {handshake.name = "constant22"} 3 : i64
    %c2_i64_9 = arith.constant {handshake.name = "constant23"} 2 : i64
    %c1_i64_10 = arith.constant {handshake.name = "constant24"} 1 : i64
    %27 = arith.extui %26 {handshake.name = "extui4"} : i32 to i64
    %28 = arith.index_cast %27 {handshake.name = "index_cast2"} : i64 to index
    %29 = memref.load %arg2[%28] {handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load2"} : memref<30xi32>
    %30 = arith.extui %26 {handshake.name = "extui5"} : i32 to i64
    %31 = arith.shli %25, %c1_i64_10 {handshake.name = "shli4"} : i64
    %32 = arith.shli %25, %c2_i64_9 {handshake.name = "shli5"} : i64
    %33 = arith.addi %31, %32 {handshake.name = "addi18"} : i64
    %34 = arith.shli %25, %c3_i64_8 {handshake.name = "shli6"} : i64
    %35 = arith.shli %25, %c4_i64_7 {handshake.name = "shli7"} : i64
    %36 = arith.addi %34, %35 {handshake.name = "addi19"} : i64
    %37 = arith.addi %33, %36 {handshake.name = "addi20"} : i64
    %38 = arith.addi %37, %30 {handshake.name = "addi4"} : i64
    %39 = arith.index_cast %38 {handshake.name = "index_cast3"} : i64 to index
    %40 = memref.load %arg0[%39] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load3"} : memref<900xi32>
    %41 = arith.subi %40, %29 {handshake.name = "subi0"} : i32
    %42 = arith.index_cast %38 {handshake.name = "index_cast4"} : i64 to index
    memref.store %41, %arg0[%42] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load5", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store4"} : memref<900xi32>
    %43 = arith.addi %26, %c1_i32_6 {handshake.name = "addi5"} : i32
    %44 = arith.cmpi ult, %43, %c30_i32_5 {handshake.name = "cmpi2"} : i32
    cf.cond_br %44, ^bb5(%43 : i32), ^bb6 {handshake.name = "cond_br2"}
  ^bb6:  // pred: ^bb5
    %c30_i32_11 = arith.constant {handshake.name = "constant25"} 30 : i32
    %c1_i32_12 = arith.constant {handshake.name = "constant26"} 1 : i32
    %c0_i32_13 = arith.constant {handshake.name = "constant27"} 0 : i32
    %45 = arith.addi %24, %c1_i32_12 {handshake.name = "addi6"} : i32
    %46 = arith.cmpi ult, %45, %c30_i32_11 {handshake.name = "cmpi3"} : i32
    cf.cond_br %46, ^bb4(%45 : i32), ^bb7(%c0_i32_13 : i32) {handshake.name = "cond_br3"}
  ^bb7(%47: i32):  // 2 preds: ^bb6, ^bb11
    cf.br ^bb8(%47 : i32) {handshake.name = "br3"}
  ^bb8(%48: i32):  // 2 preds: ^bb7, ^bb10
    %c0_i32_14 = arith.constant {handshake.name = "constant28"} 0 : i32
    %49 = arith.extui %47 {handshake.name = "extui6"} : i32 to i64
    %50 = arith.extui %48 {handshake.name = "extui7"} : i32 to i64
    cf.br ^bb9(%c0_i32_14, %c0_i32_14 : i32, i32) {handshake.name = "br4"}
  ^bb9(%51: i32, %52: i32):  // 2 preds: ^bb8, ^bb9
    %c30_i32_15 = arith.constant {handshake.name = "constant29"} 30 : i32
    %c1_i32_16 = arith.constant {handshake.name = "constant30"} 1 : i32
    %c4_i64_17 = arith.constant {handshake.name = "constant31"} 4 : i64
    %c3_i64_18 = arith.constant {handshake.name = "constant32"} 3 : i64
    %c2_i64_19 = arith.constant {handshake.name = "constant33"} 2 : i64
    %c1_i64_20 = arith.constant {handshake.name = "constant34"} 1 : i64
    %53 = arith.extui %52 {handshake.name = "extui8"} : i32 to i64
    %54 = arith.shli %53, %c1_i64_20 {handshake.name = "shli8"} : i64
    %55 = arith.shli %53, %c2_i64_19 {handshake.name = "shli9"} : i64
    %56 = arith.addi %54, %55 {handshake.name = "addi21"} : i64
    %57 = arith.shli %53, %c3_i64_18 {handshake.name = "shli10"} : i64
    %58 = arith.shli %53, %c4_i64_17 {handshake.name = "shli11"} : i64
    %59 = arith.addi %57, %58 {handshake.name = "addi22"} : i64
    %60 = arith.addi %56, %59 {handshake.name = "addi23"} : i64
    %61 = arith.addi %60, %49 {handshake.name = "addi7"} : i64
    %62 = arith.index_cast %61 {handshake.name = "index_cast5"} : i64 to index
    %63 = memref.load %arg0[%62] {handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "load5"} : memref<900xi32>
    %64 = arith.extui %52 {handshake.name = "extui9"} : i32 to i64
    %65 = arith.shli %64, %c1_i64_20 {handshake.name = "shli12"} : i64
    %66 = arith.shli %64, %c2_i64_19 {handshake.name = "shli13"} : i64
    %67 = arith.addi %65, %66 {handshake.name = "addi24"} : i64
    %68 = arith.shli %64, %c3_i64_18 {handshake.name = "shli14"} : i64
    %69 = arith.shli %64, %c4_i64_17 {handshake.name = "shli15"} : i64
    %70 = arith.addi %68, %69 {handshake.name = "addi25"} : i64
    %71 = arith.addi %67, %70 {handshake.name = "addi26"} : i64
    %72 = arith.addi %71, %50 {handshake.name = "addi8"} : i64
    %73 = arith.index_cast %72 {handshake.name = "index_cast6"} : i64 to index
    %74 = memref.load %arg0[%73] {handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "load6"} : memref<900xi32>
    %75 = arith.muli %63, %74 {handshake.name = "muli4"} : i32
    %76 = arith.addi %51, %75 {handshake.name = "addi9"} : i32
    %77 = arith.addi %52, %c1_i32_16 {handshake.name = "addi10"} : i32
    %78 = arith.cmpi ult, %77, %c30_i32_15 {handshake.name = "cmpi4"} : i32
    cf.cond_br %78, ^bb9(%76, %77 : i32, i32), ^bb10(%76 : i32) {handshake.name = "cond_br4"}
  ^bb10(%79: i32):  // pred: ^bb9
    %c30_i32_21 = arith.constant {handshake.name = "constant35"} 30 : i32
    %c1_i32_22 = arith.constant {handshake.name = "constant36"} 1 : i32
    %c4_i64_23 = arith.constant {handshake.name = "constant37"} 4 : i64
    %c3_i64_24 = arith.constant {handshake.name = "constant38"} 3 : i64
    %c2_i64_25 = arith.constant {handshake.name = "constant39"} 2 : i64
    %c1_i64_26 = arith.constant {handshake.name = "constant40"} 1 : i64
    %80 = arith.extui %47 {handshake.name = "extui10"} : i32 to i64
    %81 = arith.extui %48 {handshake.name = "extui11"} : i32 to i64
    %82 = arith.shli %80, %c1_i64_26 {handshake.name = "shli16"} : i64
    %83 = arith.shli %80, %c2_i64_25 {handshake.name = "shli17"} : i64
    %84 = arith.addi %82, %83 {handshake.name = "addi27"} : i64
    %85 = arith.shli %80, %c3_i64_24 {handshake.name = "shli18"} : i64
    %86 = arith.shli %80, %c4_i64_23 {handshake.name = "shli19"} : i64
    %87 = arith.addi %85, %86 {handshake.name = "addi28"} : i64
    %88 = arith.addi %84, %87 {handshake.name = "addi29"} : i64
    %89 = arith.addi %88, %81 {handshake.name = "addi11"} : i64
    %90 = arith.index_cast %89 {handshake.name = "index_cast7"} : i64 to index
    memref.store %79, %arg1[%90] {handshake.deps = #handshake<deps[{dstAccess : "store8", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store7"} : memref<900xi32>
    %91 = arith.extui %48 {handshake.name = "extui12"} : i32 to i64
    %92 = arith.extui %47 {handshake.name = "extui13"} : i32 to i64
    %93 = arith.shli %91, %c1_i64_26 {handshake.name = "shli20"} : i64
    %94 = arith.shli %91, %c2_i64_25 {handshake.name = "shli21"} : i64
    %95 = arith.addi %93, %94 {handshake.name = "addi30"} : i64
    %96 = arith.shli %91, %c3_i64_24 {handshake.name = "shli22"} : i64
    %97 = arith.shli %91, %c4_i64_23 {handshake.name = "shli23"} : i64
    %98 = arith.addi %96, %97 {handshake.name = "addi31"} : i64
    %99 = arith.addi %95, %98 {handshake.name = "addi32"} : i64
    %100 = arith.addi %99, %92 {handshake.name = "addi12"} : i64
    %101 = arith.index_cast %100 {handshake.name = "index_cast8"} : i64 to index
    memref.store %79, %arg1[%101] {handshake.deps = #handshake<deps[{dstAccess : "store7", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store8"} : memref<900xi32>
    %102 = arith.addi %48, %c1_i32_22 {handshake.name = "addi13"} : i32
    %103 = arith.cmpi ult, %102, %c30_i32_21 {handshake.name = "cmpi5"} : i32
    cf.cond_br %103, ^bb8(%102 : i32), ^bb11 {handshake.name = "cond_br5"}
  ^bb11:  // pred: ^bb10
    %c30_i32_27 = arith.constant {handshake.name = "constant41"} 30 : i32
    %c1_i32_28 = arith.constant {handshake.name = "constant42"} 1 : i32
    %104 = arith.addi %47, %c1_i32_28 {handshake.name = "addi14"} : i32
    %105 = arith.cmpi ult, %104, %c30_i32_27 {handshake.name = "cmpi6"} : i32
    cf.cond_br %105, ^bb7(%104 : i32), ^bb12 {handshake.name = "cond_br6"}
  ^bb12:  // pred: ^bb11
    return {handshake.name = "return0"}
  }
}

