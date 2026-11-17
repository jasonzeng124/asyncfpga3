module {
  func.func @bicg_float(%arg0: memref<900xf32> {handshake.arg_name = "A"}, %arg1: memref<30xf32> {handshake.arg_name = "s"}, %arg2: memref<30xf32> {handshake.arg_name = "q"}, %arg3: memref<30xf32> {handshake.arg_name = "p"}, %arg4: memref<30xf32> {handshake.arg_name = "r"}) -> f32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %c0_i32_0 = arith.constant {handshake.name = "constant8"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.index_cast %1 {handshake.name = "index_cast0"} : i64 to index
    %3 = memref.load %arg2[%2] {handshake.name = "load0"} : memref<30xf32>
    %4 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %5 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    cf.br ^bb2(%3, %c0_i32_0 : f32, i32) {handshake.name = "br1"}
  ^bb2(%6: f32, %7: i32):  // 2 preds: ^bb1, ^bb2
    %c30_i32 = arith.constant {handshake.name = "constant9"} 30 : i32
    %c1_i32 = arith.constant {handshake.name = "constant10"} 1 : i32
    %c4_i64 = arith.constant {handshake.name = "constant11"} 4 : i64
    %c3_i64 = arith.constant {handshake.name = "constant12"} 3 : i64
    %c2_i64 = arith.constant {handshake.name = "constant13"} 2 : i64
    %c1_i64 = arith.constant {handshake.name = "constant14"} 1 : i64
    %8 = arith.extui %7 {handshake.name = "extui3"} : i32 to i64
    %9 = arith.shli %4, %c1_i64 {handshake.name = "shli0"} : i64
    %10 = arith.shli %4, %c2_i64 {handshake.name = "shli1"} : i64
    %11 = arith.addi %9, %10 {handshake.name = "addi3"} : i64
    %12 = arith.shli %4, %c3_i64 {handshake.name = "shli2"} : i64
    %13 = arith.shli %4, %c4_i64 {handshake.name = "shli3"} : i64
    %14 = arith.addi %12, %13 {handshake.name = "addi4"} : i64
    %15 = arith.addi %11, %14 {handshake.name = "addi5"} : i64
    %16 = arith.addi %15, %8 {handshake.name = "addi0"} : i64
    %17 = arith.index_cast %16 {handshake.name = "index_cast1"} : i64 to index
    %18 = memref.load %arg0[%17] {handshake.name = "load1"} : memref<900xf32>
    %19 = arith.extui %7 {handshake.name = "extui4"} : i32 to i64
    %20 = arith.index_cast %19 {handshake.name = "index_cast2"} : i64 to index
    %21 = memref.load %arg1[%20] {handshake.name = "load2"} : memref<30xf32>
    %22 = arith.index_cast %5 {handshake.name = "index_cast3"} : i64 to index
    %23 = memref.load %arg4[%22] {handshake.name = "load3"} : memref<30xf32>
    %24 = arith.mulf %23, %18 {handshake.name = "mulf0"} : f32
    %25 = arith.addf %21, %24 {handshake.name = "addf0"} : f32
    %26 = arith.extui %7 {handshake.name = "extui5"} : i32 to i64
    %27 = arith.index_cast %26 {handshake.name = "index_cast4"} : i64 to index
    memref.store %25, %arg1[%27] {handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : memref<30xf32>
    %28 = arith.extui %7 {handshake.name = "extui6"} : i32 to i64
    %29 = arith.index_cast %28 {handshake.name = "index_cast5"} : i64 to index
    %30 = memref.load %arg3[%29] {handshake.name = "load5"} : memref<30xf32>
    %31 = arith.mulf %18, %30 {handshake.name = "mulf1"} : f32
    %32 = arith.addf %6, %31 {handshake.name = "addf1"} : f32
    %33 = arith.addi %7, %c1_i32 {handshake.name = "addi1"} : i32
    %34 = arith.cmpi ult, %33, %c30_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %34, ^bb2(%32, %33 : f32, i32), ^bb3(%32 : f32) {handshake.name = "cond_br0"}
  ^bb3(%35: f32):  // pred: ^bb2
    %c30_i32_1 = arith.constant {handshake.name = "constant15"} 30 : i32
    %c1_i32_2 = arith.constant {handshake.name = "constant16"} 1 : i32
    %36 = arith.extui %0 {handshake.name = "extui7"} : i32 to i64
    %37 = arith.index_cast %36 {handshake.name = "index_cast6"} : i64 to index
    memref.store %35, %arg2[%37] {handshake.name = "store6"} : memref<30xf32>
    %38 = arith.addi %0, %c1_i32_2 {handshake.name = "addi2"} : i32
    %39 = arith.cmpi ult, %38, %c30_i32_1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %39, ^bb1(%38 : i32), ^bb4(%35 : f32) {handshake.name = "cond_br1"}
  ^bb4(%40: f32):  // pred: ^bb3
    return {handshake.name = "return0"} %40 : f32
  }
}

