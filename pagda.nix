{ pkgs, pagda }:

{
  docs = pagda.docBackends.enhancedHtml {
    entryModule = "CategoricalCrypto";
    githubUrl = "https://github.com/input-output-hk/categorical-crypto";
  };
}
