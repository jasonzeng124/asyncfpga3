module {
  func.func @cnn(%arg0: memref<38xi32> {handshake.arg_name = "input"}, %arg1: memref<12xi32> {handshake.arg_name = "bias"}, %arg2: memref<43xi32> {handshake.arg_name = "weight"}, %arg3: memref<114xi32> {handshake.arg_name = "C"}, %arg4: memref<120xi32> {handshake.arg_name = "output"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb24
    %c1_i32 = arith.constant {handshake.name = "constant7"} 1 : i32
    %c0_i32_0 = arith.constant {handshake.name = "constant8"} 0 : i32
    %1 = arith.shli %0, %c1_i32 {handshake.name = "shli0"} : i32
    cf.br ^bb2(%c0_i32_0 : i32) {handshake.name = "br1"}
  ^bb2(%2: i32):  // 2 preds: ^bb1, ^bb6
    %c1_i32_1 = arith.constant {handshake.name = "constant9"} 1 : i32
    %c0_i32_2 = arith.constant {handshake.name = "constant10"} 0 : i32
    %c3_i32 = arith.constant {handshake.name = "constant11"} 3 : i32
    %3 = arith.shli %2, %c1_i32_1 {handshake.name = "shli4"} : i32
    %4 = arith.shli %2, %c3_i32 {handshake.name = "shli5"} : i32
    %5 = arith.addi %3, %4 {handshake.name = "addi31"} : i32
    cf.br ^bb3(%c0_i32_2 : i32) {handshake.name = "br2"}
  ^bb3(%6: i32):  // 2 preds: ^bb2, ^bb5
    %c0_i32_3 = arith.constant {handshake.name = "constant12"} 0 : i32
    cf.br ^bb4(%c0_i32_3 : i32) {handshake.name = "br3"}
  ^bb4(%7: i32):  // 2 preds: ^bb3, ^bb4
    %c2_i32 = arith.constant {handshake.name = "constant13"} 2 : i32
    %c1_i32_4 = arith.constant {handshake.name = "constant14"} 1 : i32
    %8 = arith.shli %7, %c1_i32_4 {handshake.name = "shli1"} : i32
    %9 = arith.addi %8, %5 {handshake.name = "addi0"} : i32
    %10 = arith.addi %9, %6 {handshake.name = "addi1"} : i32
    %11 = arith.addi %1, %7 {handshake.name = "addi2"} : i32
    %12 = arith.index_cast %11 {handshake.name = "index_cast0"} : i32 to index
    %13 = memref.load %arg1[%12] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : memref<12xi32>
    %14 = arith.extui %10 {handshake.name = "extui0"} : i32 to i64
    %15 = arith.index_cast %14 {handshake.name = "index_cast1"} : i64 to index
    memref.store %13, %arg3[%15] {handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store1"} : memref<114xi32>
    %16 = arith.addi %7, %c1_i32_4 {handshake.name = "addi3"} : i32
    %17 = arith.cmpi ult, %16, %c2_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %17, ^bb4(%16 : i32), ^bb5 {handshake.name = "cond_br0"}
  ^bb5:  // pred: ^bb4
    %c10_i32 = arith.constant {handshake.name = "constant15"} 10 : i32
    %c1_i32_5 = arith.constant {handshake.name = "constant16"} 1 : i32
    %18 = arith.addi %6, %c1_i32_5 {handshake.name = "addi4"} : i32
    %19 = arith.cmpi ult, %18, %c10_i32 {handshake.name = "cmpi1"} : i32
    cf.cond_br %19, ^bb3(%18 : i32), ^bb6 {handshake.name = "cond_br1"}
  ^bb6:  // pred: ^bb5
    %c10_i32_6 = arith.constant {handshake.name = "constant17"} 10 : i32
    %c1_i32_7 = arith.constant {handshake.name = "constant18"} 1 : i32
    %c0_i32_8 = arith.constant {handshake.name = "constant19"} 0 : i32
    %20 = arith.addi %2, %c1_i32_7 {handshake.name = "addi5"} : i32
    %21 = arith.cmpi ult, %20, %c10_i32_6 {handshake.name = "cmpi2"} : i32
    cf.cond_br %21, ^bb2(%20 : i32), ^bb7(%c0_i32_8 : i32) {handshake.name = "cond_br2"}
  ^bb7(%22: i32):  // 2 preds: ^bb6, ^bb17
    %c0_i32_9 = arith.constant {handshake.name = "constant20"} 0 : i32
    cf.br ^bb8(%c0_i32_9 : i32) {handshake.name = "br4"}
  ^bb8(%23: i32):  // 2 preds: ^bb7, ^bb16
    %c1_i32_10 = arith.constant {handshake.name = "constant21"} 1 : i32
    %c0_i32_11 = arith.constant {handshake.name = "constant22"} 0 : i32
    %c3_i32_12 = arith.constant {handshake.name = "constant23"} 3 : i32
    %24 = arith.addi %22, %23 {handshake.name = "addi6"} : i32
    %25 = arith.shli %23, %c1_i32_10 {handshake.name = "shli6"} : i32
    %26 = arith.shli %23, %c3_i32_12 {handshake.name = "shli7"} : i32
    %27 = arith.addi %25, %26 {handshake.name = "addi32"} : i32
    cf.br ^bb9(%c0_i32_11 : i32) {handshake.name = "br5"}
  ^bb9(%28: i32):  // 2 preds: ^bb8, ^bb15
    %c0_i32_13 = arith.constant {handshake.name = "constant24"} 0 : i32
    cf.br ^bb10(%c0_i32_13 : i32) {handshake.name = "br6"}
  ^bb10(%29: i32):  // 2 preds: ^bb9, ^bb14
    %c1_i32_14 = arith.constant {handshake.name = "constant25"} 1 : i32
    %c0_i32_15 = arith.constant {handshake.name = "constant26"} 0 : i32
    %30 = arith.addi %0, %29 {handshake.name = "addi7"} : i32
    %31 = arith.addi %30, %22 {handshake.name = "addi8"} : i32
    %32 = arith.shli %29, %c1_i32_14 {handshake.name = "shli2"} : i32
    %33 = arith.addi %32, %27 {handshake.name = "addi9"} : i32
    %34 = arith.addi %33, %28 {handshake.name = "addi10"} : i32
    %35 = arith.extui %34 {handshake.name = "extui1"} : i32 to i64
    %36 = arith.index_cast %35 {handshake.name = "index_cast2"} : i64 to index
    %37 = memref.load %arg3[%36] {handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load2"} : memref<114xi32>
    cf.br ^bb11(%c0_i32_15, %37 : i32, i32) {handshake.name = "br7"}
  ^bb11(%38: i32, %39: i32):  // 2 preds: ^bb10, ^bb13
    %c0_i32_16 = arith.constant {handshake.name = "constant27"} 0 : i32
    %40 = arith.addi %24, %38 {handshake.name = "addi11"} : i32
    %41 = arith.addi %40, %28 {handshake.name = "addi12"} : i32
    cf.br ^bb12(%c0_i32_16, %39 : i32, i32) {handshake.name = "br8"}
  ^bb12(%42: i32, %43: i32):  // 2 preds: ^bb11, ^bb12
    %c4_i32 = arith.constant {handshake.name = "constant28"} 4 : i32
    %c1_i32_17 = arith.constant {handshake.name = "constant29"} 1 : i32
    %44 = arith.addi %31, %42 {handshake.name = "addi13"} : i32
    %45 = arith.addi %44, %38 {handshake.name = "addi14"} : i32
    %46 = arith.addi %41, %42 {handshake.name = "addi15"} : i32
    %47 = arith.extui %45 {handshake.name = "extui2"} : i32 to i64
    %48 = arith.index_cast %47 {handshake.name = "index_cast3"} : i64 to index
    %49 = memref.load %arg2[%48] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load3"} : memref<43xi32>
    %50 = arith.extui %46 {handshake.name = "extui3"} : i32 to i64
    %51 = arith.index_cast %50 {handshake.name = "index_cast4"} : i64 to index
    %52 = memref.load %arg0[%51] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load4"} : memref<38xi32>
    %53 = arith.muli %49, %52 {handshake.name = "muli2"} : i32
    %54 = arith.addi %43, %53 {handshake.name = "addi16"} : i32
    %55 = arith.index_cast %35 {handshake.name = "index_cast5"} : i64 to index
    memref.store %54, %arg3[%55] {handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 3>, handshake.name = "store5"} : memref<114xi32>
    %56 = arith.addi %42, %c1_i32_17 {handshake.name = "addi17"} : i32
    %57 = arith.cmpi ult, %56, %c4_i32 {handshake.name = "cmpi3"} : i32
    cf.cond_br %57, ^bb12(%56, %54 : i32, i32), ^bb13(%54 : i32) {handshake.name = "cond_br3"}
  ^bb13(%58: i32):  // pred: ^bb12
    %c4_i32_18 = arith.constant {handshake.name = "constant30"} 4 : i32
    %c1_i32_19 = arith.constant {handshake.name = "constant31"} 1 : i32
    %59 = arith.addi %38, %c1_i32_19 {handshake.name = "addi18"} : i32
    %60 = arith.cmpi ult, %59, %c4_i32_18 {handshake.name = "cmpi4"} : i32
    cf.cond_br %60, ^bb11(%59, %58 : i32, i32), ^bb14 {handshake.name = "cond_br4"}
  ^bb14:  // pred: ^bb13
    %c2_i32_20 = arith.constant {handshake.name = "constant32"} 2 : i32
    %c1_i32_21 = arith.constant {handshake.name = "constant33"} 1 : i32
    %61 = arith.addi %29, %c1_i32_21 {handshake.name = "addi19"} : i32
    %62 = arith.cmpi ult, %61, %c2_i32_20 {handshake.name = "cmpi5"} : i32
    cf.cond_br %62, ^bb10(%61 : i32), ^bb15 {handshake.name = "cond_br5"}
  ^bb15:  // pred: ^bb14
    %c10_i32_22 = arith.constant {handshake.name = "constant34"} 10 : i32
    %c1_i32_23 = arith.constant {handshake.name = "constant35"} 1 : i32
    %63 = arith.addi %28, %c1_i32_23 {handshake.name = "addi20"} : i32
    %64 = arith.cmpi ult, %63, %c10_i32_22 {handshake.name = "cmpi6"} : i32
    cf.cond_br %64, ^bb9(%63 : i32), ^bb16 {handshake.name = "cond_br6"}
  ^bb16:  // pred: ^bb15
    %c10_i32_24 = arith.constant {handshake.name = "constant36"} 10 : i32
    %c1_i32_25 = arith.constant {handshake.name = "constant37"} 1 : i32
    %65 = arith.addi %23, %c1_i32_25 {handshake.name = "addi21"} : i32
    %66 = arith.cmpi ult, %65, %c10_i32_24 {handshake.name = "cmpi7"} : i32
    cf.cond_br %66, ^bb8(%65 : i32), ^bb17 {handshake.name = "cond_br7"}
  ^bb17:  // pred: ^bb16
    %c10_i32_26 = arith.constant {handshake.name = "constant38"} 10 : i32
    %c1_i32_27 = arith.constant {handshake.name = "constant39"} 1 : i32
    %67 = arith.addi %22, %c1_i32_27 {handshake.name = "addi22"} : i32
    %68 = arith.cmpi ult, %67, %c10_i32_26 {handshake.name = "cmpi8"} : i32
    cf.cond_br %68, ^bb7(%67 : i32), ^bb18 {handshake.name = "cond_br8"}
  ^bb18:  // pred: ^bb17
    %c2_i32_28 = arith.constant {handshake.name = "constant40"} 2 : i32
    %c0_i32_29 = arith.constant {handshake.name = "constant41"} 0 : i32
    %69 = arith.shli %0, %c2_i32_28 {handshake.name = "shli8"} : i32
    %70 = arith.addi %0, %69 {handshake.name = "addi33"} : i32
    cf.br ^bb19(%c0_i32_29 : i32) {handshake.name = "br9"}
  ^bb19(%71: i32):  // 2 preds: ^bb18, ^bb23
    %c1_i32_30 = arith.constant {handshake.name = "constant42"} 1 : i32
    %c0_i32_31 = arith.constant {handshake.name = "constant43"} 0 : i32
    %c3_i32_32 = arith.constant {handshake.name = "constant44"} 3 : i32
    %72 = arith.shli %71, %c1_i32_30 {handshake.name = "shli9"} : i32
    %73 = arith.shli %71, %c3_i32_32 {handshake.name = "shli10"} : i32
    %74 = arith.addi %72, %73 {handshake.name = "addi34"} : i32
    %75 = arith.shli %71, %c1_i32_30 {handshake.name = "shli11"} : i32
    %76 = arith.shli %71, %c3_i32_32 {handshake.name = "shli12"} : i32
    %77 = arith.addi %75, %76 {handshake.name = "addi35"} : i32
    %78 = arith.addi %70, %77 {handshake.name = "addi23"} : i32
    cf.br ^bb20(%c0_i32_31 : i32) {handshake.name = "br10"}
  ^bb20(%79: i32):  // 2 preds: ^bb19, ^bb22
    %c0_i32_33 = arith.constant {handshake.name = "constant45"} 0 : i32
    %80 = arith.addi %78, %79 {handshake.name = "addi24"} : i32
    %81 = arith.extui %80 {handshake.name = "extui4"} : i32 to i64
    cf.br ^bb21(%c0_i32_33 : i32) {handshake.name = "br11"}
  ^bb21(%82: i32):  // 2 preds: ^bb20, ^bb21
    %c2_i32_34 = arith.constant {handshake.name = "constant46"} 2 : i32
    %c1_i32_35 = arith.constant {handshake.name = "constant47"} 1 : i32
    %c0_i32_36 = arith.constant {handshake.name = "constant48"} 0 : i32
    %83 = arith.shli %82, %c1_i32_35 {handshake.name = "shli3"} : i32
    %84 = arith.addi %83, %74 {handshake.name = "addi25"} : i32
    %85 = arith.addi %84, %79 {handshake.name = "addi26"} : i32
    %86 = arith.extui %85 {handshake.name = "extui5"} : i32 to i64
    %87 = arith.index_cast %86 {handshake.name = "index_cast6"} : i64 to index
    %88 = memref.load %arg3[%87] {handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "load6"} : memref<114xi32>
    %89 = arith.cmpi sgt, %88, %c0_i32_36 {handshake.name = "cmpi9"} : i32
    %90 = arith.select %89, %88, %c0_i32_36 {handshake.name = "select0"} : i32
    %91 = arith.index_cast %81 {handshake.name = "index_cast7"} : i64 to index
    memref.store %90, %arg4[%91] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store7"} : memref<120xi32>
    %92 = arith.addi %82, %c1_i32_35 {handshake.name = "addi27"} : i32
    %93 = arith.cmpi ult, %92, %c2_i32_34 {handshake.name = "cmpi10"} : i32
    cf.cond_br %93, ^bb21(%92 : i32), ^bb22 {handshake.name = "cond_br9"}
  ^bb22:  // pred: ^bb21
    %c10_i32_37 = arith.constant {handshake.name = "constant49"} 10 : i32
    %c1_i32_38 = arith.constant {handshake.name = "constant50"} 1 : i32
    %94 = arith.addi %79, %c1_i32_38 {handshake.name = "addi28"} : i32
    %95 = arith.cmpi ult, %94, %c10_i32_37 {handshake.name = "cmpi11"} : i32
    cf.cond_br %95, ^bb20(%94 : i32), ^bb23 {handshake.name = "cond_br10"}
  ^bb23:  // pred: ^bb22
    %c10_i32_39 = arith.constant {handshake.name = "constant51"} 10 : i32
    %c1_i32_40 = arith.constant {handshake.name = "constant52"} 1 : i32
    %96 = arith.addi %71, %c1_i32_40 {handshake.name = "addi29"} : i32
    %97 = arith.cmpi ult, %96, %c10_i32_39 {handshake.name = "cmpi12"} : i32
    cf.cond_br %97, ^bb19(%96 : i32), ^bb24 {handshake.name = "cond_br11"}
  ^bb24:  // pred: ^bb23
    %c5_i32 = arith.constant {handshake.name = "constant53"} 5 : i32
    %c1_i32_41 = arith.constant {handshake.name = "constant54"} 1 : i32
    %98 = arith.addi %0, %c1_i32_41 {handshake.name = "addi30"} : i32
    %99 = arith.cmpi ult, %98, %c5_i32 {handshake.name = "cmpi13"} : i32
    cf.cond_br %99, ^bb1(%98 : i32), ^bb25 {handshake.name = "cond_br12"}
  ^bb25:  // pred: ^bb24
    return {handshake.name = "return0"}
  }
}

