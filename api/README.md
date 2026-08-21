# Public API baselines

These snapshot files back the `Public API` job in `.github/workflows/rust.yml`.

They intentionally cover the stable public surfaces of `ion-rs`:

- default features
- `bigdecimal` delta relative to the default feature set

The `bigdecimal` file is stored as a sorted set difference instead of a second full
snapshot so review stays small and line position does not matter. This feature only
adds API items on top of the default surface, so set semantics are enough here.

The `experimental*` feature sets are excluded because those APIs are documented as unstable.
The API baselines are pinned to `nightly-2026-06-02` because `cargo-public-api` output
changes across nightly toolchains.

To regenerate these baselines after an intentional stable API change:

```bash
cargo install --locked cargo-public-api --version 0.52.0
PATH="$HOME/.cargo/bin:$PATH" RUSTUP_TOOLCHAIN=nightly-2026-06-02 cargo public-api -p ion-rs -sss --color never > api/default.txt
PATH="$HOME/.cargo/bin:$PATH" RUSTUP_TOOLCHAIN=nightly-2026-06-02 cargo public-api -p ion-rs -sss --features bigdecimal --color never > /tmp/bigdecimal.txt
LC_ALL=C sort -u api/default.txt > /tmp/default-sorted.txt
LC_ALL=C sort -u /tmp/bigdecimal.txt > /tmp/bigdecimal-sorted.txt
comm -13 /tmp/default-sorted.txt /tmp/bigdecimal-sorted.txt > api/bigdecimal.txt
```

If your `cargo` binary is not managed by `rustup`, invoke the rustup proxy explicitly:

```bash
PATH="$HOME/.cargo/bin:$PATH" RUSTUP_TOOLCHAIN=nightly-2026-06-02 ~/.cargo/bin/cargo public-api -p ion-rs -sss --color never > api/default.txt
PATH="$HOME/.cargo/bin:$PATH" RUSTUP_TOOLCHAIN=nightly-2026-06-02 ~/.cargo/bin/cargo public-api -p ion-rs -sss --features bigdecimal --color never > /tmp/bigdecimal.txt
LC_ALL=C sort -u api/default.txt > /tmp/default-sorted.txt
LC_ALL=C sort -u /tmp/bigdecimal.txt > /tmp/bigdecimal-sorted.txt
comm -13 /tmp/default-sorted.txt /tmp/bigdecimal-sorted.txt > api/bigdecimal.txt
```
