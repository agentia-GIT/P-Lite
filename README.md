# P-Lite — Lecteur A/V

Lecteur audio/vidéo Windows natif, léger et rapide (C + Win32, libmpv chargée dynamiquement), livré en un seul `.exe`.

## Fonctions
- Lecture audio/vidéo, mode fenêtre / plein écran, barre de pistes audio et sous-titres
- IPTV : listes M3U (dossier `iptv`), sélecteurs Langue / Catégorie / Chaîne, webradios (fond animé réactif à la musique)
- Capture écran / zone / fenêtre + son du PC (FFmpeg, x265)
- Paramètres : versions des bibliothèques (libmpv, FFmpeg) et mises à jour en un clic, mise à jour de l'application depuis un zip (listes et configuration conservées)

## Compilation (mingw-w64, depuis Linux)
```
./build.sh
```
Produit `lecteur.exe` (nécessite `x86_64-w64-mingw32-gcc` et `x86_64-w64-mingw32-windres`). Le `lecteur.exe` à jour est aussi fourni dans ce dépôt à chaque build.

## Utilisation
Placer `lecteur.exe` dans un dossier avec `iptv\` (listes). `libmpv` et FFmpeg sont téléchargés au démarrage dans `codec\` s'ils manquent.

Les playlists dont le nom commence par `Musique` sont classées comme webradios.
