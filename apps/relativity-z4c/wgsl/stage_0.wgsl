// obend-emit-gpu: BonaMassoZ4c1D, stage 0 of 2: 55 kernels, 880 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<vec2<u32>>;
@group(0) @binding(1) var<storage, read> c : array<vec2<u32>>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;


fn u32_mul_wide(a: u32, b: u32) -> vec2<u32> {
  // Bounded u32 operands: the backend emits native low/high u32 products.
  let product = u64(a) * u64(b);
  return vec2<u32>(u32(product), u32(product >> 32u));
}
fn u64_add(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
  let lo = a.x + b.x;
  return vec2<u32>(lo, a.y + b.y + select(0u, 1u, lo < a.x));
}
fn u64_sub(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
  return vec2<u32>(a.x - b.x, a.y - b.y - select(0u, 1u, a.x < b.x));
}
fn u64_lt(a: vec2<u32>, b: vec2<u32>) -> bool {
  return a.y < b.y || (a.y == b.y && a.x < b.x);
}
fn u64_mul(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
  let p = u32_mul_wide(a.x, b.x);
  return vec2<u32>(p.x, p.y + a.x * b.y + a.y * b.x);
}
fn u64_shr(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
  if (b.y != 0u || b.x >= 64u) { return vec2<u32>(0u); }
  if (b.x == 0u) { return a; }
  if (b.x >= 32u) { return vec2<u32>(a.y >> (b.x - 32u), 0u); }
  return vec2<u32>((a.x >> b.x) | (a.y << (32u - b.x)), a.y >> b.x);
}
fn u64_shl(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
  if (b.y != 0u || b.x >= 64u) { return vec2<u32>(0u); }
  if (b.x == 0u) { return a; }
  if (b.x >= 32u) { return vec2<u32>(0u, a.x << (b.x - 32u)); }
  return vec2<u32>(a.x << b.x, (a.y << b.x) | (a.x >> (32u - b.x)));
}

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x + gid.y * 896u;
  if (t < 16u) {
    let e : u32 = t - 0u;
    w[96u + e] = w[0u + ix[0u + e]];
  }
  if (t >= 16u && t < 32u) {
    let e : u32 = t - 16u;
    w[112u + e] = w[0u + ix[16u + e]];
  }
  if (t >= 32u && t < 48u) {
    let e : u32 = t - 32u;
    w[128u + e] = w[0u + ix[32u + e]];
  }
  if (t >= 48u && t < 64u) {
    let e : u32 = t - 48u;
    w[144u + e] = w[0u + ix[48u + e]];
  }
  if (t >= 64u && t < 80u) {
    let e : u32 = t - 64u;
    w[160u + e] = w[0u + ix[64u + e]];
  }
  if (t >= 80u && t < 96u) {
    let e : u32 = t - 80u;
    w[176u + e] = c[0u + e];
  }
  if (t >= 96u && t < 112u) {
    let e : u32 = t - 96u;
    w[192u + e] = c[16u + e];
  }
  if (t >= 112u && t < 128u) {
    let e : u32 = t - 112u;
    w[208u + e] = c[32u + e];
  }
  if (t >= 128u && t < 144u) {
    let e : u32 = t - 128u;
    w[224u + e] = w[16u + ix[80u + e]];
  }
  if (t >= 144u && t < 160u) {
    let e : u32 = t - 144u;
    w[240u + e] = w[16u + ix[96u + e]];
  }
  if (t >= 160u && t < 176u) {
    let e : u32 = t - 160u;
    w[256u + e] = w[16u + ix[112u + e]];
  }
  if (t >= 176u && t < 192u) {
    let e : u32 = t - 176u;
    w[272u + e] = w[16u + ix[128u + e]];
  }
  if (t >= 192u && t < 208u) {
    let e : u32 = t - 192u;
    w[288u + e] = w[16u + ix[144u + e]];
  }
  if (t >= 208u && t < 224u) {
    let e : u32 = t - 208u;
    w[304u + e] = w[32u + ix[160u + e]];
  }
  if (t >= 224u && t < 240u) {
    let e : u32 = t - 224u;
    w[320u + e] = w[32u + ix[176u + e]];
  }
  if (t >= 240u && t < 256u) {
    let e : u32 = t - 240u;
    w[336u + e] = w[32u + ix[192u + e]];
  }
  if (t >= 256u && t < 272u) {
    let e : u32 = t - 256u;
    w[352u + e] = w[32u + ix[208u + e]];
  }
  if (t >= 272u && t < 288u) {
    let e : u32 = t - 272u;
    w[368u + e] = w[32u + ix[224u + e]];
  }
  if (t >= 288u && t < 304u) {
    let e : u32 = t - 288u;
    w[384u + e] = w[48u + ix[240u + e]];
  }
  if (t >= 304u && t < 320u) {
    let e : u32 = t - 304u;
    w[400u + e] = w[48u + ix[256u + e]];
  }
  if (t >= 320u && t < 336u) {
    let e : u32 = t - 320u;
    w[416u + e] = w[48u + ix[272u + e]];
  }
  if (t >= 336u && t < 352u) {
    let e : u32 = t - 336u;
    w[432u + e] = w[48u + ix[288u + e]];
  }
  if (t >= 352u && t < 368u) {
    let e : u32 = t - 352u;
    w[448u + e] = w[48u + ix[304u + e]];
  }
  if (t >= 368u && t < 384u) {
    let e : u32 = t - 368u;
    w[464u + e] = w[64u + ix[320u + e]];
  }
  if (t >= 384u && t < 400u) {
    let e : u32 = t - 384u;
    w[480u + e] = w[64u + ix[336u + e]];
  }
  if (t >= 400u && t < 416u) {
    let e : u32 = t - 400u;
    w[496u + e] = w[64u + ix[352u + e]];
  }
  if (t >= 416u && t < 432u) {
    let e : u32 = t - 416u;
    w[512u + e] = w[64u + ix[368u + e]];
  }
  if (t >= 432u && t < 448u) {
    let e : u32 = t - 432u;
    w[528u + e] = w[64u + ix[384u + e]];
  }
  if (t >= 448u && t < 464u) {
    let e : u32 = t - 448u;
    w[544u + e] = w[80u + ix[400u + e]];
  }
  if (t >= 464u && t < 480u) {
    let e : u32 = t - 464u;
    w[560u + e] = w[80u + ix[416u + e]];
  }
  if (t >= 480u && t < 496u) {
    let e : u32 = t - 480u;
    w[576u + e] = w[80u + ix[432u + e]];
  }
  if (t >= 496u && t < 512u) {
    let e : u32 = t - 496u;
    w[592u + e] = w[80u + ix[448u + e]];
  }
  if (t >= 512u && t < 528u) {
    let e : u32 = t - 512u;
    w[608u + e] = w[80u + ix[464u + e]];
  }
  if (t >= 528u && t < 544u) {
    let e : u32 = t - 528u;
    w[624u + e] = c[48u + e];
  }
  if (t >= 544u && t < 560u) {
    let e : u32 = t - 544u;
    w[640u + e] = c[64u + e];
  }
  if (t >= 560u && t < 576u) {
    let e : u32 = t - 560u;
    w[656u + e] = c[80u + e];
  }
  if (t >= 576u && t < 592u) {
    let e : u32 = t - 576u;
    w[672u + e] = c[96u + e];
  }
  if (t >= 592u && t < 608u) {
    let e : u32 = t - 592u;
    w[688u + e] = c[112u + e];
  }
  if (t >= 608u && t < 624u) {
    let e : u32 = t - 608u;
    w[704u + e] = c[128u + e];
  }
  if (t >= 624u && t < 640u) {
    let e : u32 = t - 624u;
    w[720u + e] = c[144u + e];
  }
  if (t >= 640u && t < 656u) {
    let e : u32 = t - 640u;
    w[736u + e] = c[160u + e];
  }
  if (t >= 656u && t < 672u) {
    let e : u32 = t - 656u;
    w[752u + e] = c[176u + e];
  }
  if (t >= 672u && t < 688u) {
    let e : u32 = t - 672u;
    w[768u + e] = c[192u + e];
  }
  if (t >= 688u && t < 704u) {
    let e : u32 = t - 688u;
    w[784u + e] = c[208u + e];
  }
  if (t >= 704u && t < 720u) {
    let e : u32 = t - 704u;
    w[800u + e] = c[224u + e];
  }
  if (t >= 720u && t < 736u) {
    let e : u32 = t - 720u;
    w[816u + e] = c[240u + e];
  }
  if (t >= 736u && t < 752u) {
    let e : u32 = t - 736u;
    w[832u + e] = c[256u + e];
  }
  if (t >= 752u && t < 768u) {
    let e : u32 = t - 752u;
    w[848u + e] = c[272u + e];
  }
  if (t >= 768u && t < 784u) {
    let e : u32 = t - 768u;
    w[864u + e] = c[288u + e];
  }
  if (t >= 784u && t < 800u) {
    let e : u32 = t - 784u;
    w[880u + e] = c[304u + e];
  }
  if (t >= 800u && t < 816u) {
    let e : u32 = t - 800u;
    w[896u + e] = c[320u + e];
  }
  if (t >= 816u && t < 832u) {
    let e : u32 = t - 816u;
    w[912u + e] = c[336u + e];
  }
  if (t >= 832u && t < 848u) {
    let e : u32 = t - 832u;
    w[928u + e] = c[352u + e];
  }
  if (t >= 848u && t < 864u) {
    let e : u32 = t - 848u;
    w[944u + e] = c[368u + e];
  }
  if (t >= 864u && t < 880u) {
    let e : u32 = t - 864u;
    w[960u + e] = c[384u + e];
  }
}
