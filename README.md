# Формальная философия

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
  [AgdaIntro.agda](https://github.com/odomanov/formal-philosophy/blob/main/AgdaIntro.agda)
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
- Файлы проверены на Agda 2.6.0.1 без использования библиотек помимо
  Builtin (кроме IntensionalLogic и Meta, требующих stdlib 1.2).
