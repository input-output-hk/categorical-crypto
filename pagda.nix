{ pkgs, pagda }:

{
  docs = pagda.docBackends.enhancedHtml {
    modules = [
      "CategoricalCrypto"
      "Categories.Discrete"
      "Categories.FreeMonoidal"
      "Categories.FreeStrictMonoidal"
      "Categories.GradedKleisli"
      "Categories.MonoidalCoherence"
      "Categories.NaturalTransformationHelper"
      "Categories.Properties"
      "Class.Monad.Ext"
    ];
    entryModule = "CategoricalCrypto";
    githubUrl = "https://github.com/input-output-hk/categorical-crypto";
    backButtonUrl = "index.html";
  };
}
