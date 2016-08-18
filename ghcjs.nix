{ reflex-platform, ... }: reflex-platform.ghcjs.override {
  overrides = self: super: {
    SimpleFP-v2 = self.callPackage ./SimpleFP-v2 {};
  };
}
