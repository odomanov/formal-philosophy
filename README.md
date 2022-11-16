# Формальная философия

<details>
<summary>Оглавление</summary>
<!-- markdown-toc start - Don't edit this section. Run M-x markdown-toc-refresh-toc -->

- [Формальная философия](#формальная-философия)
    - [Установка Агды и общая информация](#установка-агды-и-общая-информация)
    - [Приблизительный план занятий](#приблизительный-план-занятий)
        - [Введение и основные определения](#введение-и-основные-определения)
        - [Разные формализации](#разные-формализации)
        - [Формализации языков логики](#формализации-языков-логики)
        - [Формализации естественного языка](#формализации-естественного-языка)
        - [Другие файлы](#другие-файлы)

<!-- markdown-toc end -->
</details>

## Установка Агды и общая информация

- Установка Agda в Windows: http://homepage.divms.uiowa.edu/~astump/agda/
  (нужно установить Agda2.6.0.1.v1.msi).  
  
  После установки в главном меню появится пункт «Emacs for Agda», это
  редактор Emacs, настроенный для работы с Агдой. Кроме того, файлы с
  расширением .agda будут по умолчанию открываться в этом редакторе. Работа
  с Emacs описана в документации:
  https://agda.readthedocs.io/en/latest/tools/emacs-mode.html.
- Другие способы установки:
  https://agda.readthedocs.io/en/latest/getting-started/installation.html.
- Файл
  [AgdaIntro.agda](AgdaIntro.agda)
  содержит очень краткое введение в Агду.
- Полезная информация об Агде:
    - Документация: https://agda.readthedocs.io/en/v2.6.0./ (НЕ
      последняя версия!).
    - [Programming Language Foundations in Agda](https://plfa.github.io/)
    - Учебники, лекции и пр.:
      https://agda.readthedocs.io/en/latest/getting-started/tutorial-list.html.
    - Статьи с использованием Агды:
      https://wiki.portal.chalmers.se/agda/Main/PapersUsingAgda.
    - [Introduction to Univalent Foundations of Mathematics with
      Agda](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html)
- Комбинации клавиш в Emacs:
  https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#keybindings.
  
  Основные комбинации: 
    - C-c C-l, то есть Ctrl-c Ctrl-l (можно держать Ctrl и последовательно
      нажать `c` и `l`). Это проверка корректности открытого файла и
      его исполнение.
    - C-c C-n — нормализация, то есть сведение к нормальной форме, то
      есть вычисление.
- Печать символов Юникода:
  https://people.inf.elte.hu/divip/AgdaTutorial/Symbols.html.
- Файлы проверены на Agda 2.6.0.1.  Файлам корневой директории не нужны
  библиотеки помимо Builtin. Остальные файлы требуют установки stdlib 1.2.

## Приблизительный план занятий

Звёздочкой отмечены факультативные разделы.

### Введение и основные определения

- [AgdaIntro.agda](AgdaIntro.agda) — Введение в язык Agda.
- [TT.agda](TT.agda) — Основные определения теории типов.
- [TTCore.agda](TTCore.agda) — «Библиотека»: основные определения,
  используемые в других файлах.

### Разные формализации

- [Choice.agda](Choice.agda) — Аксиома выбора. 
- [Peano.agda](Peano.agda) — Натуральные числа и аксиоматика Пеано. 
- [CrossWorld.agda](CrossWorld.agda) — Кросс-мировая предикация. 
- [RussellParadox.agda](RussellParadox.agda) — Формализация парадокса Рассела. 
- [Subsets.agda](Subsets.agda) — Подмножества одного
  множества. Вспомогательный файл для
  [GeneralizedQuantifiersKS.agda](GeneralizedQuantifiersKS.agda).
- [Syllogism.agda](Syllogism.agda) — Силлогизмы.  
- *[Order.agda](Order.agda) — Структуры порядка. 
- *[Tree.agda](Tree.agda) — Деревья и работа с ними. 
- *[Graph.agda](Graph.agda) — Формализация графов.

### Формализации языков логики

Суффикс `-Meta` обозначает использование Агды как метаязыка.

- [SimpleLanguage-Meta.agda](Meta/SimpleLanguage-Meta.agda) — Демонстрация
  разных способов формализации языков на примере очень простого языка.
- [PropositionalLogic.agda](PropositionalLogic.agda) — Пропозициональная логика. 
- [PropositionalLogic-Meta.agda](PropositionalLogic-Meta.agda) —
  Пропозициональная логика. 
- [LambdaCalculus-Meta.agda](Meta/LambdaCalculus-Meta.agda) —
  Лямбда-исчисление.
- [LambdaCalculus2-Meta.agda](Meta/LambdaCalculus-Meta2.agda) —
  Лямбда-исчисление. Термы индексируются типами, то есть
  сразу определяются как корректные.
- [FOL.agda](FOL.agda) — Логика первого порядка. 
- *[FOL-Meta.agda](Meta/FOL-Meta.agda) — Логика первого порядка.
- [FOLModal-Meta.agda](Meta/FOLModal-Meta.agda) — Логика первого порядка с
  модальными операторами.
- [GeneralizedQuantifiersKS.agda](GeneralizedQuantifiersKS.agda) —
  Обобщённые кванторы (см. также
  *[GeneralizedQuantifiersBC.agda](GeneralizedQuantifiersBC.agda)).
- *[IF-logic.agda](IF-logic.agda) — Independence friendly logic Хинтикки.

### Формализации естественного языка 

- [Montague.agda](Montague.agda) — Семантика Монтегю. Стандартное изложение. 
- [MontagueTT.agda](MontagueTT.agda) — Семантика Монтегю. Интерпретация в
  теории типов (см. также
  *[MontagueTTcoercion.agda](MontagueTTcoercion.agda) — Семантика Монтегю в
  теории типов с коэрсией).
- [AbstractSyntax.agda](AbstractSyntax.agda) — Представление синтаксиса в
  теории типов.
- (продолжение следует...)

### Другие файлы

- [Nat.agda](Nat.agda) — `TTCore` не содержит определений для
  натуральных чисел. Они вынесены в отдельный файл.
- *[Fin.agda](Fin.agda) — Определение типа `Fin n` (для справки). 
- *[Coercion.agda](Coercion.agda) — Определения для работы с коэрсией.
- *[IntensionalLogic](IntensionalLogic) — Формализация интенсиональной
  логики с помощью монад.
