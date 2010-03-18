import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.Iterator;

/**
 * Pequeno programa cliente que prueba la funcionalidad  y operatividad del tipo
 * ConsultOrt en todas las variantes de su implementacion. Programa desarrollado
 * para el proyecto de la materia "Algoritmos y Estructuras II" de la Universi-
 * dad Simon Bolivar, dictada en el periodo Enero-Marzo por el profesor Diego 
 * Mosquera.
 * 
 * Proyecto desarrollado en los lenguajes:
 * 
 * JAVA:
 * java version "1.4.2_18"
 * Java(TM) 2 Runtime Environment, Standard Edition (build 1.4.2_18-b06)
 * Java HotSpot(TM) Client VM (build 1.4.2_18-b06, mixed mode)
 * 
 * JML:
 * 
 * jml version 5.4
 * 
 * @author Victor De Ponte, Carnet 05-38087
 * @author Jose Zabala,     Carnet 05-39070
 * 
 * @Historial_de_Versiones:
 * 
 * @version 0.1  -  01/03/2010
 *                  PRIMER AVANCE... estan implementadas nada mas las 4 primeras
 *                  opciones, correspondientes a la variante del tipo implemen-
 *                  tada con arreglos. Maneja eficientemente las excepciones 
 *                  lanzadas por las operaciones.
 *                  
 * @version 0.2  -  11/03/2010
 *                  SEGUNDO AVANCE... implementadas todas las opciones, junto 
 *                  con los gestores de las nuevas excepciones utilizadas.
 */
public class ConsultorOrtografico {
    
    // METODOS AUXILIARES:
    /* Pequenos metodos que se encargan de implementar opciones del menu de 
     * especial dimension y/o complejidad. No tienen especificacion en JML 
     * debido a que ejecutan instrucciones mas propias del lenguaje JAVA, muy
     * dificiles (si no imposibles) de especificar usando el lenguaje JML. Sin
     * embargo, todas tienen un pequeno comentario antes de la firma (en 
     * javadoc) en el cual se menciona la funcionalidad y operatividad de cada 
     * uno...
     */
    
    /**
     * Metodo estatico que imprime en la salida estandar un arreglo de Strings.
     * @param a Arreglo de Strings a imprimir
     */
    public static void print (String[] a ) {
        System.out.println("\nEl arreglo es:\n\n");
        System.out.print("[");
        if (a.length > 0) {
            /*@ loop_invariant true;
            @ decreasing a.length - 1 - k;
            @*/
            for (int k = 0; k < a.length - 1; k++) {
                System.out.print(" " + a[k] + ",");
            }
            System.out.print(" "+a[a.length-1]+" ");
        }
        System.out.print("]\n");
    }
    
    /**
     * Cuenta las lineas que tiene un archivo, pasandolo a traves de un 
     * BufferedReader.
     * @param f el nombre del archivo
     * @return el numero de lineas del archivo f
     */
    public static int countLines (String f) {
        BufferedReader  br = null;
        String linea="";
        boolean stop = false;
        int l = 0;
        try{
            br = new BufferedReader(new FileReader(f));
        } catch (IOException e) {
            e.getMessage();
            System.out.println("Hubo un error al abrir el archivo \n\n      \""+f+"\"\n\nNo se encuentra...");
        }
        while (!stop) {
            try {
                linea = br.readLine();
                if (linea == null) {
                    stop = true;
                } else {
                    l++;
                }
            } catch (IOException e) {
                System.out.println("Ocurrio un error al separar en lineas el archivo \n\n      \""+f+"\"\n\nMientras se leia la linea: "+l);
                System.out.println(e.getMessage());
                System.out.println("Esta linea sera ignorada...\nContinuando la carga del archivo...");
            }
        }
        return l;
    }
    
    
    /**
     * Se encarga de cargar un vocabulario entero a partir de un archivo de 
     * texto plano, utilizando un BufferedReader
     * @param c de tipo ConsultOrt. El Consultor Ortografico donde se van a 
     *          agregar las palabras del vocabulario
     * @param f de tipo String. El nombre del archivo a cargar.
     * @return un arreglo de "long" de tamano 2, donde almacena el tiempo neto 
     *         (en milisegundos) usado por el metodo "agregar" en la primera 
     *         posicion, y el tiempo total usado por todo el metoda "loadFile" 
     *         para terminar su ejecucion (en milisegundos).
     * @throws ExcepcionArchivoNoExiste si el archivo 'f' no existe
     * @throws ExcepcionNoEsArchivo si el archivo 'f' no es un archivo
     * @throws ExcepcionArchivoNoSePuedeLeer si el archivo 'f' no se puede leer
     */
    public static long[] loadFile (ConsultOrt c, String f) throws 
            ExcepcionArchivoNoExiste,
            ExcepcionNoEsArchivo,
            ExcepcionArchivoNoSePuedeLeer 
    {
        long initTime = System.currentTimeMillis();
        long[] time = new long[2];
        long timeSum = 0;
        String errOut = "";
        String linea="";
        if ((new File(f)).exists() && 
            (new File(f)).isFile() && 
            (new File(f)).canRead())
        {
            BufferedReader  br = null;
            int l = 1;
            int nLines = countLines(f);
            double stepAt = (nLines/100);
            double counter = 0.0;
            try{
                br = new BufferedReader(new FileReader(f));
            } catch (IOException e) {
                errOut = errOut + e.getMessage();
                errOut = errOut +"\n"+"Hubo un error al abrir el archivo \n\n      \""+f+"\"\n\nNo se encuentra...\n";
            }
            boolean stop = false;
            l = 1;
            long startTime = 0;
            long stopTime = 0;
            System.out.println("\nComienza el proceso de carga del archivo \""+f+"\"...\n");
            System.out.println("Progreso:\n");
            System.out.print("[");
            do {
                try {
                    linea = br.readLine();
                    if (linea == null) {
                        stop = true;
                    } else {
                        try {
                                startTime = System.currentTimeMillis();
                                c.agregar(linea);
                                stopTime = System.currentTimeMillis();
                                timeSum = timeSum + (stopTime - startTime);
                                if ( (l <= nLines/2 ) && (stepAt <= counter) ) {
                                    counter = 0.0;
                                    System.out.print("#");
                                } else if ( (l <= (nLines*3)/4 ) && (stepAt/2 <= counter) ) {
                                    counter = 0.0;
                                    System.out.print("#");
                                } else if ( (l <= (nLines*7)/8 ) && (stepAt/4 <= counter) ) {
                                    counter = 0.0;
                                    System.out.print("#");
                                } else if ( (l <= (nLines*15)/16 ) && (stepAt/8 <= counter) ) {
                                    counter = 0.0;
                                    System.out.print("#");
                                } else if ( (l <= (nLines*31)/32 ) && (stepAt/16 <= counter) ) {
                                    counter = 0.0;
                                    System.out.print("#");
                                } else {
                                    counter = counter + 1.0;
                                }
                        } catch (ExcepcionPalabraNoBienFormada ex) {
                            errOut = errOut +"\n"+"(Linea "+l+") \""+linea+"\" es una palabra mal formada...";
                            errOut = errOut +"\n"+"Esta linea sera ignorada...\nSe continua con la carga del archivo...\n";
                        } catch (ExcepcionPalabraYaRegistrada ex) {
                            errOut = errOut +"\n"+"(Linea "+l+") "+ex.gerMessage();
                            errOut = errOut +"\n"+"Esta linea sera ignorada...\nContinuando la carga del archivo...\n";
                        }
                    }
                } catch (IOException e) {
                    errOut = errOut +"\n"+"Ocurrio un error al separar en lineas el archivo \n\n      \""+f+"\"\n\nMientras se leia la linea: "+l;
                    errOut = errOut +"\n"+e.getMessage();
                    errOut = errOut +"\n"+"Esta linea sera ignorada...\nContinuando la carga del archivo...\n";
                }
                l++;
            } while (!stop);
            System.out.print("] 100%\n");
            System.out.println("\nLa carga del archivo \""+f+"\" ha sido completada exitosamente!!!\n");
        } else if (!(new File(f)).exists()) {
            throw new ExcepcionArchivoNoExiste("El archivo \""+f+"\" no existe...");
        } else if (!(new File(f)).isFile()) {
            throw new ExcepcionNoEsArchivo("El archivo \""+f+"\" no es un archivo...");
        } else if (!(new File(f)).canRead()) {
            throw new ExcepcionArchivoNoSePuedeLeer("El archivo \""+f+"\" no se puede leer...");
        }
        if (!errOut.equals("")) {
            System.out.println("Ocurrieron algunos errores durante la carga...");
            System.out.println("Estos errores pueden no ser graves, pero conviene revisarlos...");
            do {
                linea = Console.readString("\n Ud desea revisar los errores? (s/n)\n\n    >>   ");
            } while ( !linea.equalsIgnoreCase("s") && !linea.equalsIgnoreCase("n") );
            if (linea.equalsIgnoreCase("s")) {
                System.out.println("\nSALIDA DE ERROR:\n\n" + errOut+"\n");
            }
        }
        time[0] = timeSum;
        long endTime = System.currentTimeMillis();
        time[1] = (endTime - initTime);
        return time;
    }
    
    public static void cargarArchivo(ConsultOrt c, String l, boolean variante) {
        boolean excepcion = false;
        long[] tiempo = new long[2];
        l = Console.readString("\nPor favor introduzca el nombre del archivo a leer:\n\n    >>   ");
        do {
            try {
                tiempo = loadFile(c, l);
            } catch (ExcepcionArchivoNoExiste ex) {
                System.out.println("\n"+ex.gerMessage());
                l = gestorArchivoNoExiste(c, l);
                excepcion = true;
            } catch (ExcepcionNoEsArchivo ex) {
                System.out.println("\n"+ex.gerMessage());
                l = gestorNoEsArchivo(c, l);
                excepcion = true;
            } catch (ExcepcionArchivoNoSePuedeLeer ex) {
                System.out.println("\n"+ex.gerMessage());
                l = gestorArchivoNoSePuedeLeer(c, l);
                excepcion = true;
            }
        } while (excepcion);
        Long netTime = new Long(tiempo[0]);
        Long totalTime = new Long(tiempo[1]);
        double nt = netTime.doubleValue()/1000;
        double tt = totalTime.doubleValue()/1000;
        double di = tt - nt;
        long diff = tiempo[1] - tiempo[0];
        do {
            l = Console.readString("\n Ud desea ver el informe de tiempo de ejecucion? (s/n)\n\n    >>   ");
        } while ( !l.equalsIgnoreCase("s") && !l.equalsIgnoreCase("n") );
        if (l.equalsIgnoreCase("s")) {
            System.out.println("\nINFORME DEL TIEMPO DE EJECUCION:");
            System.out.println("\nEl tiempo neto usado por el metodo \"agregar\", implementado con la variante "+( variante ? "\"Arreglos\"" : "\"Tries\"" )+" es de "+nt+" segundos ("+tiempo[0]+" milisegundos)...");
            System.out.println("\nEl tiempo total usado por el metodo \"loadFile\", implementado con la variante "+( variante ? "\"Arreglos\"" : "\"Tries\"" )+" es de "+tt+" segundos ("+tiempo[1]+" milisegundos)...");
            System.out.println("\nLa diferencia entre el tiempo usado por los metodos \"loadFile\" y \"agregar\", implementados con la variante "+( variante ? "\"Arreglos\"" : "\"Tries\"" )+" es de "+di+" segundos ("+diff+" milisegundos)...");
        }
    }
    
    /**
     * Procedimiento encargado de listar todas las palabras contenidas en el 
     * vocabulario del ConsultOrt pasado como parametro. Para ello, se vale de 
     * la implementacion de iterador en el tipo.
     * @param c de tipo ConsultOrt. El Consultor Ortografico cuyo vocabulario se
     *                              va a listar.
     */
    public static void listarVoc (ConsultOrt c,boolean variante){
        if (variante) {
            Iterator e = c.elems();
            if (e.hasNext()) {
                System.out.println("\nEl vocabulario de este Consultor Ortografico contiene las palabras:\n");
                while (e.hasNext()) {
                    System.out.println(e.next());
                }
                System.out.println("\nFin del vocabulario...");
            } else {
                System.out.println("\nEl vocabulario esta vacio...");
            }
        } else {
            System.out.println("\n      Lo Sentimos!!!!\nEl iterador para esta variante no esta implementado...\n");
        }
    }
    
    // GESTORES DE EXCEPCIONES:
    /* Pequenos procedimientos que hacen mas facil la interaccion del usuario 
     * final con una situacion de excepcion. Guian al usuario a resolver la 
     * situacion o lo aconsejan acerca de proximas entradas que deba hacer. Son 
     * parte de los metodos auxiliares de este programa...
     */
    
    /**
     * Se encarga de manejar la situacion de excepcion PalabraNoBienFormada. 
     * muestra al usuario las normas para construir una palabra bien formada, y 
     * luego lo redirige al programa principal, donde se le solicitara una nueva
     * palabra.
     * @param c de tipo ConsultOrt. Consultor ortografico en uso
     * @param p de tipo String. Palabra invalida originalmente escrita por el 
     *        usuario.
     */
    public static void gestorMalFormada (ConsultOrt c, String p) {
        System.out.println("\nUd ha entrado al manejador de la excepcion:\n\n");
        System.out.println("      \"ExcepcionPalabraNoBienFormada\"");
        System.out.println("\n\nLa palabra que ud introdujo ("+p+"), no esta bien formada.");
        System.out.println("para que este bien formada, debe de contener al menos una letra del alfabeto");
        System.out.println("ingles, utilizando solo las letras minusculas, sin numeros ni signos de\npuntuacion...\n\n");
        System.out.println("Este mensaje aparecera cada vez que ud ingrese una palabra mal formada...");
        System.out.println("Ahora que Ud. conoce las reglas para formar una palabra,");
        System.out.println("Por favor, Introduzca una palabra bien formada...");
    }
    
    /**
     * Se encarga de manejar la situacion de excepcion PalabraYaRegistrada. 
     * ofrece al usuario la posibilidad de consultar el vocabulario, para asi 
     * saber cuales palabras ya pertenecen a el, para no agregarlas de nuevo al 
     * momento de ser solicitada una nueva palabra a agregar.
     * @param c de tipo ConsultOrt. Consultor ortografico en uso
     * @param p de tipo String. Palabra invalida originalmente escrita por el 
     *        usuario.
     */
    public static void gestorYaRegistrada (ConsultOrt c, String p) {
        System.out.println("\nUd ha entrado al manejador de la excepcion:\n\n");
        System.out.println("       \"ExcepcionPalabraYaRegistrada\"");
        System.out.println("\n\nUd entrara en este manejador cada vez que ingrese una palabra que ya este registrada...");
        System.out.println("La palabra que ud introdujo ("+p+"), ya pertenece al vocabulario del Consultor\nOrtografico en uso...");
        System.out.println("Consulte el vocabulario usando prefijos para ver las palabras que ya estan registradas,\ny luego ingrese una que no este en el vocabulario...");
        String s = "";
        String cont = "";
        do {
            s = Console.readString("\n\nPor favor, Introduzca un prefijo a consultar (palabra bien formada):\n\n   >>  ");
            if (!c.bf(s)) {
                System.out.println("Esta palabra esta mal formada...");
            } else {
                try {
                    System.out.println("\nConsultando el vocabulario con el prefijo \""+s+"\"...");
                    String[] a = c.consultarPorPrefijo(s);
                    System.out.println("Consulta generada!!!");
                    print(a);
                    do {
                        cont = Console.readString("\nDesea continuar consultando el vocabulario??? (y/n):\n\n    >>   ");
                    } while (!cont.equalsIgnoreCase("y") && !cont.equalsIgnoreCase("n"));
                } catch (ExcepcionPalabraNoBienFormada ex) {
                    System.out.println(ex.gerMessage());
                    gestorMalFormada(c, p);
                }
            }
        } while (!c.bf(s) || cont.equalsIgnoreCase("y"));
        System.out.println("Ahora que ha consultado el vocabulario, por favor ingrese una palabra que no\neste registrada...");
    }
    
    /**
     * Se encarga de manejar la situacion de excepcion ArchivoNoExiste. Pide al
     * usuario un nuevo nombre de archivo, hasta que ese nombre sea valido
     * @param c de tipo ConsultOrt. Consultor ortografico en uso
     * @param p de tipo String. Nombre de archivo originalmente escrito por el 
     *        usuario
     * @return un String que contiene un nuevo nombre de archivo valido.
     */
    public static String gestorArchivoNoExiste (ConsultOrt c, String p) {
        System.out.println("\nUd ha entrado al manejador de la excepcion:\n\n");
        System.out.println("       \"ExcepcionArchivoNoExiste\"");
        System.out.println("\n\nEl archivo que ud introdujo\n\n  \""+p+"\"\n");
        System.out.println("no existe...\n");
        String f;
        do {
            System.out.println("Por favor ingrese un nuevo nobre de archivo");
            System.out.println("El gestor lo prevendra de si el archivo  es un archivo valido o no...");
            f = Console.readString("\n\n    >>   ");
            if ( (!(new File(f)).isFile()) || 
                 (!(new File(f)).canRead())||
                 (!(new File(f)).exists())
               ) {
                System.out.println("\nEste archivo tampoco es valido...\n");
            }
        } while (!(new File(f)).exists());
        return f;
    }
    
    /**
     * Se encarga de manejar la situacion de excepcion NoEsArchivo. Pide al
     * usuario un nuevo nombre de archivo, hasta que ese nombre sea valido
     * @param c de tipo ConsultOrt. Consultor ortografico en uso
     * @param p de tipo String. Nombre de archivo originalmente escrito por el 
     *        usuario
     * @return un String que contiene un nuevo nombre de archivo valido.
     */
    public static String gestorNoEsArchivo (ConsultOrt c, String p) {
        System.out.println("\nUd ha entrado al manejador de la excepcion:\n\n");
        System.out.println("       \"ExcepcionNoEsArchivo\"");
        System.out.println("\n\nEl archivo que ud introdujo\n\n  \""+p+"\"\n");
        System.out.println("no es un archivo...\n");
        String f;
        do {
            System.out.println("Por favor ingrese un nuevo nobre de archivo");
            System.out.println("El gestor lo prevendra de si el archivo  es un archivo valido o no...");
            f = Console.readString("\n\n    >>   ");
            if ( (!(new File(f)).isFile()) || 
                 (!(new File(f)).canRead())||
                 (!(new File(f)).exists())
               ) {
                System.out.println("\nEste archivo tampoco es valido...\n");
            }
        } while ( (!(new File(f)).isFile()) || 
                  (!(new File(f)).canRead())||
                  (!(new File(f)).exists()) 
                );
        return f;
    }
    
    /**
     * Se encarga de manejar la situacion de excepcion ArchivoNoSePuedeLeer. 
     * Pide al usuario un nuevo nombre de archivo, hasta que ese nombre sea
     * valido.
     * @param c de tipo ConsultOrt. Consultor ortografico en uso
     * @param p de tipo String. Nombre de archivo originalmente escrito por el 
     *        usuario
     * @return un String que contiene un nuevo nombre de archivo valido.
     */
    public static String gestorArchivoNoSePuedeLeer (ConsultOrt c, String p) {
        System.out.println("\nUd ha entrado al manejador de la excepcion:\n\n");
        System.out.println("       \"ExcepcionArchivoNoSePuedeLeer\"");
        System.out.println("\n\nEl archivo que ud introdujo\n\n  \""+p+"\"\n");
        System.out.println("no se puede leer...\n");
        String f;
        do {
            System.out.println("Por favor ingrese un nuevo nobre de archivo");
            System.out.println("El gestor lo prevendra de si el archivo  es un archivo valido o no...");
            f = Console.readString("\n\n    >>   ");
            if ( (!(new File(f)).isFile()) || 
                 (!(new File(f)).canRead())||
                 (!(new File(f)).exists())
               ) {
                System.out.println("\nEste archivo tampoco es valido...\n");
            }
        } while ( (!(new File(f)).isFile()) || 
                  (!(new File(f)).canRead())||
                  (!(new File(f)).exists()) 
                );
        return f;
    }
    
    public static void gestorNoSuchElement () {
        System.out.println("\nUd ha entrado al manejador de la excepcion:\n\n");
        System.out.println("       \"NoSuchElementException\"");
        System.out.println("Esto nunca deberia ocurrir, contacte al programador...\n");
    }
    
    // FIN DE LOS GESTORES DE EXCEPCIONES...
    
    // FIN DE LOS METODOS AUXILIARES...
    
    public static void main (String[] args) {
        
        /* @Historial_de_Versiones:
 * 
 * @version 0.1  -  01/03/2010
 *                  PRIMER AVANCE... estan implementadas nada mas las 4 primeras
 *                  opciones, correspondientes a la variante del tipo implemen-
 *                  tada con arreglos. Maneja eficientemente las excepciones 
 *                  lanzadas por las operaciones.
 *                  
 * @version 0.2  -  11/03/2010
 *                  SEGUNDO AVANCE... implementadas todas las opciones, junto 
 *                  con los gestores de las nuevas excepciones utilizadas.
 */
        System.out.println("\nBienvenido al programa de prueba del tipo:\n");
        System.out.println("           \"Consultor Ortografico\"");
        System.out.println("                 (ConsultOrt)");
        System.out.println("\nEste tipo abstracto ha sido desarrollado por:\n\n");
        System.out.println("    *Victor Manuel De Ponte Olivares        Carnet 05-38087");
        System.out.println("    *Jose Carlos Zabala                     Carnet 05-39070");
        System.out.println("\n\nBasado en codigo fuente escrito por el profesor Diego Mosquera");
        System.out.println("\nVersion de prueba 0.1");
        System.out.println("\nHistorial de versiones:\n");
        System.out.println("0.1  -  01/03/2010");
        System.out.println("        PRIMER AVANCE... estan implementadas nada mas las 4 primeras");
        System.out.println("        opciones, correspondientes a la variante del tipo implemen-");
        System.out.println("        tada con arreglos. Maneja eficientemente las excepciones lan-");
        System.out.println("        zadas por las operaciones.\n");
        System.out.println("0.2  -  11/03/2010");
        System.out.println("        SEGUNDO AVANCE... implementadas todas las opciones para la va-");
        System.out.println("        riante implementada con arreglos. Usando la variante con tries,");
        System.out.println("        solo estan activas las opciones 1,2 y 3. Tambien se implementa-");
        System.out.println("        ron los gestores de las nuevas excepciones utilizadas.");
        int opc=0;
        ConsultOrt c = new ConsultOrtArreglos();
        boolean creado = false;
        boolean variante = true; // true si se usa arreglos, false si se usa tries
        boolean volver = false;
        do {
            String l = "";
            System.out.println("\n\nMENU:\n\n");
            System.out.println("1) Crear un nuevo Consultor Ortografico vacio");
            System.out.println("2) Agregar palabras al vocabulario del consultor");
            System.out.println("3) Consultar las palabras del vocabulario por medio de un prefijo");
            System.out.println("4) Generar el prefijo mas largo valido a partir de una palabra");
            System.out.println("5) Cargar un vocabulario completo a partir de un archivo, midiendo el tiempo de carga");
            System.out.println("6) Listar todas las palabras del vocabulario del consultor ortografico");
            System.out.println("7) Salir del programa de prueba del tipo \"Consultor Ortografico\"");
            opc = Console.readInt("\nQue desea Hacer??\n\n Introduzca una opcion valida:\n\n>> ");
            if (opc == 1) {
                do {
                    System.out.println("\n\nCual variante desea usar???\n");
                    System.out.println("1) La variante  implementada con ARREGLOS");
                    System.out.println("2) La variante implementada con TRIES");
                    System.out.println("3) Volver al menu anterior...");
                    int v = Console.readInt("\n\n Introduzca una opcion valida:\n\n>> ");
                    if (v == 1) {
                        c = new ConsultOrtArreglos();
                        creado = true;
                        variante = true;
                    } else if (v == 2) {
                        c = new ConsultOrtTriesArreglos();
                        creado = true;
                        variante = false;
                        //System.out.println("\n              LO SENTIMOS!!!\nVariante no implementada todavia...");
                    } else if (v == 3) {
                        volver = true;
                        System.out.println("volviendo...");
                    }
                } while (!creado && !volver);
                System.out.println("\nConsultor Ortografico vacio creado con exito...");
            } else if (opc == 2) {
                if (creado) {
                    int n;
                    do {
                        n = Console.readInt("\nCuantas palabras quiere agregar?\n\n    >>   ");
                    } while (!(0 < n));
                    String[] palabras = new String[n];
                    for (int k =0; k < palabras.length; k++) {
                        palabras[k] = Console.readString("\nIntroduzca la "+(k+1)+"a palabra a agregar:\n\n         >>   ");
                    }
                    for (int k = 0; k < palabras.length; k++){
                        System.out.println("\nAgregando la palabra \"" + palabras[k] + "\"...");
                        try {
                            c.agregar(palabras[k]);
                            System.out.println("\nPalabra \"" + palabras[k] + "\" agregada con exito!!!");
                        } catch (ExcepcionPalabraNoBienFormada ex) {
                            System.out.println(ex.gerMessage());
                            gestorMalFormada(c,palabras[k]);
                        } catch (ExcepcionPalabraYaRegistrada ex) {
                            System.out.println(ex.gerMessage());
                            gestorYaRegistrada(c,palabras[k]);
                        }
                    }
                } else {
                    System.out.println("\nNo se ha creado un nuevo Consultor Ortografico, no es posible realizar la operacion...");
                }
            } else if (opc == 3) {
                if (creado) {
                    do {
                        l = Console.readString("\nIntroduzca el prefijo a consultar:\n\n    >>   ");
                        try {
                            System.out.println("\nConsultando el vocabulario con el prefijo \""+l+"\"...");
                            String[] a = c.consultarPorPrefijo(l);
                            System.out.println("\nArreglo de palabras en el vocabulario para el prefijo \"" + l + "\"\ncreado con exito!!!");
                            print(a);
                        } catch (ExcepcionPalabraNoBienFormada ex) {
                            System.out.println(ex.gerMessage());
                            gestorMalFormada(c,l);
                        }
                    } while (!c.bf(l));
                } else {
                    System.out.println("\nNo se ha creado un nuevo Consultor Ortografico, no es posible realizar la operacion...");
                }
            } else if (opc == 4) {
                if (creado) {
                    do {
                        l = Console.readString("\nIntroduzca la palabra a partir de la cual se generara el prefijo:\n\n    >>   ");
                        try {
                            System.out.println("\nGenerando el prefijo mas largo posible a partir de  \"" + l + "\"...");
                            String s = c.prefijoMasLargo(l);
                            System.out.println("\nPrefijo mas largo a partir de la palabra \"" + l + "\" generado con exito!!!");
                            System.out.println("\nEl prefijo generado es:\n\n\n       >>          \""+s+"\"");
                        } catch (ExcepcionPalabraNoBienFormada ex) {
                            System.out.println(ex.gerMessage());
                            gestorMalFormada(c,l);
                        }
                    } while (!c.bf(l));
                } else {
                    System.out.println("\nNo se ha creado un nuevo Consultor Ortografico, no es posible realizar la operacion...");
                }
            } else if (opc == 5) {
                if (creado) {
                    cargarArchivo(c, l, variante);
                    System.out.println("\nFin del proceso de carga...\n");
                } else {
                    System.out.println("\nNo se ha creado un nuevo Consultor Ortografico, no es posible realizar la operacion...");
                }
            } else if (opc == 6) {
                if (creado) {
                    listarVoc(c,variante);
                } else {
                    System.out.println("\nNo se ha creado un nuevo Consultor Ortografico, no es posible realizar la operacion...");
                }
            } else if (opc == 7) {
                System.out.println("\nGracias por probar el tipo \"Consultor Ortografico\"....");
                System.out.println("\nEste tipo abstracto ha sido desarrollado por:\n\n");
                System.out.println("    *Victor Manuel De Ponte Olivares        Carnet 05-38087");
                System.out.println("    *Jose Carlos Zabala                     Carnet 05-39070");
                System.out.println("\n\nBasado en codigo fuente escrito por el profesor Diego Mosquera");
                System.out.println("\nVersion de prueba 0.1");
                System.out.println("\nHasta Luego!!!....\n\n");
                opc = 0;
            } else {
                System.out.println("\nUd. introdujo una opcion incorrecta....");
                opc = 1;
            }
        } while (1 <= opc && opc <= 7);
    }
}