{ reflex-platform, ... }: reflex-platform.ghc.override {
  overrides = self: super: {
    morte = self.callPackage ./Haskell-Morte-Library {};
  };
}
