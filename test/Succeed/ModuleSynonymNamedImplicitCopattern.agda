module ModuleSynonymNamedImplicitCopattern where

record Cat : Set₁ where
  field
    Obj  : Set
    Hom  : Obj → Obj → Set
    id   : ∀ {x} → Hom x x

record Functor (A B : Cat) : Set where
  field
    obj-map : Cat.Obj A → Cat.Obj B
    hom-map : ∀ {x y} → Cat.Hom A x y → Cat.Hom B (obj-map x) (obj-map y)

record Transformation {A B : Cat} (F G : Functor A B) : Set where
  field
    η : (x : Cat.Obj A) → Cat.Hom B (Functor.obj-map F x) (Functor.obj-map G x)

-- Named-implicit synonym in copattern clause, with grouped {module A B : Cat}
id-trans : ∀ {module A B : Cat} (F : Functor A B)
         → Transformation F F
id-trans {B = B with Cat module} F .Transformation.η x = B.id
