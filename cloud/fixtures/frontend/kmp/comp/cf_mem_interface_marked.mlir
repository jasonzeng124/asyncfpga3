module {
  func.func @kmp(%arg0: memref<4xi8> {handshake.arg_name = "pattern"}, %arg1: memref<1000xi8> {handshake.arg_name = "input"}, %arg2: memref<4xi32> {handshake.arg_name = "kmpNext"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %c1_i32 = arith.constant {handshake.name = "constant1"} 1 : i32
    %c0 = arith.constant {handshake.name = "constant6"} 0 : index
    memref.store %c0_i32, %arg2[%c0] {handshake.deps = #handshake<deps[{dstAccess : "load10", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store0"} : memref<4xi32>
    cf.br ^bb1(%c0_i32, %c1_i32 : i32, i32) {handshake.name = "br0"}
  ^bb1(%0: i32, %1: i32):  // 2 preds: ^bb0, ^bb4
    %c0_i32_0 = arith.constant {handshake.name = "constant7"} 0 : i32
    %2 = arith.extui %1 {handshake.name = "extui0"} : i32 to i64
    %3 = arith.index_cast %2 {handshake.name = "index_cast0"} : i64 to index
    %4 = memref.load %arg0[%3] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : memref<4xi8>
    %5 = arith.cmpi sgt, %0, %c0_i32_0 {handshake.name = "cmpi0"} : i32
    cf.cond_br %5, ^bb2(%0 : i32), ^bb4(%0 : i32) {handshake.name = "cond_br0"}
  ^bb2(%6: i32):  // 2 preds: ^bb1, ^bb3
    %7 = arith.index_cast %6 {handshake.name = "index_cast1"} : i32 to index
    %8 = memref.load %arg0[%7] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load2"} : memref<4xi8>
    %9 = arith.cmpi eq, %8, %4 {handshake.name = "cmpi1"} : i8
    cf.cond_br %9, ^bb4(%6 : i32), ^bb3 {handshake.name = "cond_br1"}
  ^bb3:  // pred: ^bb2
    %c0_i32_1 = arith.constant {handshake.name = "constant8"} 0 : i32
    %10 = arith.extui %1 {handshake.name = "extui1"} : i32 to i64
    %11 = arith.index_cast %10 {handshake.name = "index_cast2"} : i64 to index
    %12 = memref.load %arg2[%11] {handshake.deps = #handshake<deps[{dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "load3"} : memref<4xi32>
    %13 = arith.cmpi sgt, %12, %c0_i32_1 {handshake.name = "cmpi2"} : i32
    cf.cond_br %13, ^bb2(%12 : i32), ^bb4(%12 : i32) {handshake.name = "cond_br2"}
  ^bb4(%14: i32):  // 3 preds: ^bb1, ^bb2, ^bb3
    %c4_i32 = arith.constant {handshake.name = "constant9"} 4 : i32
    %c1_i32_2 = arith.constant {handshake.name = "constant10"} 1 : i32
    %c0_i32_3 = arith.constant {handshake.name = "constant11"} 0 : i32
    %15 = arith.index_cast %14 {handshake.name = "index_cast3"} : i32 to index
    %16 = memref.load %arg0[%15] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load4"} : memref<4xi8>
    %17 = arith.cmpi eq, %16, %4 {handshake.name = "cmpi3"} : i8
    %18 = arith.addi %14, %c1_i32_2 {handshake.name = "addi0"} : i32
    %19 = arith.select %17, %18, %14 {handshake.name = "select0"} : i32
    %20 = arith.extui %1 {handshake.name = "extui2"} : i32 to i64
    %21 = arith.index_cast %20 {handshake.name = "index_cast4"} : i64 to index
    memref.store %19, %arg2[%21] {handshake.deps = #handshake<deps[{dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load8", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load10", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 3>, handshake.name = "store5"} : memref<4xi32>
    %22 = arith.addi %1, %c1_i32_2 {handshake.name = "addi1"} : i32
    %23 = arith.cmpi ult, %22, %c4_i32 {handshake.name = "cmpi4"} : i32
    cf.cond_br %23, ^bb1(%19, %22 : i32, i32), ^bb5(%c0_i32_3, %c0_i32_3, %c0_i32_3 : i32, i32, i32) {handshake.name = "cond_br3"}
  ^bb5(%24: i32, %25: i32, %26: i32):  // 2 preds: ^bb4, ^bb10
    %c0_i32_4 = arith.constant {handshake.name = "constant12"} 0 : i32
    %27 = arith.extui %26 {handshake.name = "extui3"} : i32 to i64
    %28 = arith.index_cast %27 {handshake.name = "index_cast5"} : i64 to index
    %29 = memref.load %arg1[%28] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load6"} : memref<1000xi8>
    %30 = arith.cmpi sgt, %25, %c0_i32_4 {handshake.name = "cmpi5"} : i32
    cf.cond_br %30, ^bb6(%25 : i32), ^bb8(%25 : i32) {handshake.name = "cond_br4"}
  ^bb6(%31: i32):  // 2 preds: ^bb5, ^bb7
    %32 = arith.index_cast %31 {handshake.name = "index_cast6"} : i32 to index
    %33 = memref.load %arg0[%32] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load7"} : memref<4xi8>
    %34 = arith.cmpi eq, %33, %29 {handshake.name = "cmpi6"} : i8
    cf.cond_br %34, ^bb8(%31 : i32), ^bb7 {handshake.name = "cond_br5"}
  ^bb7:  // pred: ^bb6
    %c0_i32_5 = arith.constant {handshake.name = "constant13"} 0 : i32
    %35 = arith.index_cast %31 {handshake.name = "index_cast7"} : i32 to index
    %36 = memref.load %arg2[%35] {handshake.mem_interface = #handshake.mem_interface<LSQ: 4>, handshake.name = "load8"} : memref<4xi32>
    %37 = arith.cmpi sgt, %36, %c0_i32_5 {handshake.name = "cmpi7"} : i32
    cf.cond_br %37, ^bb6(%36 : i32), ^bb8(%36 : i32) {handshake.name = "cond_br6"}
  ^bb8(%38: i32):  // 3 preds: ^bb5, ^bb6, ^bb7
    %c3_i32 = arith.constant {handshake.name = "constant14"} 3 : i32
    %c1_i32_6 = arith.constant {handshake.name = "constant15"} 1 : i32
    %39 = arith.index_cast %38 {handshake.name = "index_cast8"} : i32 to index
    %40 = memref.load %arg0[%39] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load9"} : memref<4xi8>
    %41 = arith.cmpi eq, %40, %29 {handshake.name = "cmpi8"} : i8
    %42 = arith.addi %38, %c1_i32_6 {handshake.name = "addi2"} : i32
    %43 = arith.select %41, %42, %38 {handshake.name = "select1"} : i32
    %44 = arith.cmpi sgt, %43, %c3_i32 {handshake.name = "cmpi9"} : i32
    cf.cond_br %44, ^bb9, ^bb10(%43, %24 : i32, i32) {handshake.name = "cond_br7"}
  ^bb9:  // pred: ^bb8
    %c-1_i32 = arith.constant {handshake.name = "constant16"} -1 : i32
    %c1_i32_7 = arith.constant {handshake.name = "constant17"} 1 : i32
    %45 = arith.addi %24, %c1_i32_7 {handshake.name = "addi3"} : i32
    %46 = arith.addi %43, %c-1_i32 {handshake.name = "addi4"} : i32
    %47 = arith.index_cast %46 {handshake.name = "index_cast9"} : i32 to index
    %48 = memref.load %arg2[%47] {handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load10"} : memref<4xi32>
    cf.br ^bb10(%48, %45 : i32, i32) {handshake.name = "br1"}
  ^bb10(%49: i32, %50: i32):  // 2 preds: ^bb8, ^bb9
    %c1000_i32 = arith.constant {handshake.name = "constant18"} 1000 : i32
    %c1_i32_8 = arith.constant {handshake.name = "constant19"} 1 : i32
    %51 = arith.addi %26, %c1_i32_8 {handshake.name = "addi5"} : i32
    %52 = arith.cmpi ult, %51, %c1000_i32 {handshake.name = "cmpi10"} : i32
    cf.cond_br %52, ^bb5(%50, %49, %51 : i32, i32, i32), ^bb11(%50 : i32) {handshake.name = "cond_br8"}
  ^bb11(%53: i32):  // pred: ^bb10
    return {handshake.name = "return0"} %53 : i32
  }
}

