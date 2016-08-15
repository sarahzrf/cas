{ reflex-platform, ... }: reflex-platform.ghcjs.override {
  overrides = self: super: {
    morte = self.callPackage ./Haskell-Morte-Library {};
  };
}
