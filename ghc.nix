{ reflex-platform, ... }: reflex-platform.ghc.override {
  overrides = self: super: {
    SimpleFP-v2 = self.callPackage ./SimpleFP-v2 {};
  };
}
