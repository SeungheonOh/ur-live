(* Cards have independent editable sources. The board derives its filtered
   columns and counts from signals; moving a card does not lose its draft. *)
datatype stage = Todo | Doing | Done
type card = {Id : int, Title : source string, Draft : source string, Stage : source stage}

fun stageName stage =
    case stage of Todo => "To do" | Doing => "Doing" | Done => "Done"

fun nextStage stage =
    case stage of Todo => Doing | Doing => Done | Done => Todo

fun lower text =
    let
        fun loop i =
            if i >= strlen text then ""
            else str1 (tolower (strsub text i)) ^ loop (i + 1)
    in loop 0 end

fun matches query title =
    query = "" || (case strsindex (lower title) (lower query) of None => False | Some _ => True)

fun main () : transaction page =
    first <- source "Sketch the game";
    second <- source "Build a playable prototype";
    third <- source "Make something in Ur";
    firstDraft <- source "Sketch the game";
    secondDraft <- source "Build a playable prototype";
    thirdDraft <- source "Make something in Ur";
    firstStage <- source Todo;
    secondStage <- source Doing;
    thirdStage <- source Done;
    cards <- source ({Id = 1, Title = first, Draft = firstDraft, Stage = firstStage} ::
                     {Id = 2, Title = second, Draft = secondDraft, Stage = secondStage} ::
                     {Id = 3, Title = third, Draft = thirdDraft, Stage = thirdStage} :: []);
    nextId <- source 4;
    draft <- source "";
    query <- source "";
    message <- source "";
    let
        fun add () =
            title <- get draft;
            current <- get cards;
            if title = "" then set message "Give the card a title."
            else if List.length current >= 40 then set message "This little board holds 40 cards."
            else
                id <- get nextId;
                titleSource <- source title;
                draftSource <- source title;
                stageSource <- source Todo;
                set cards (List.append current ({Id = id, Title = titleSource,
                    Draft = draftSource, Stage = stageSource} :: []));
                set nextId (id + 1);
                set draft "";
                set message ""

        fun remove id =
            current <- get cards;
            set cards (List.filter (fn card => card.Id <> id) current)

        fun column target =
            current <- signal cards;
            search <- signal query;
            visible <- List.filterM (fn card =>
                title <- signal card.Title;
                stage <- signal card.Stage;
                return (stageName stage = stageName target && matches search title)) current;
            content <- List.mapXM (fn card =>
                title <- signal card.Title;
                return <xml>
                <div style="padding:12px;margin:8px 0;border:1px solid #cbd5e1;border-radius:8px;background:#f8fafc">
                  <p><strong>{[title]}</strong></p>
                  <label>Edit title: <ctextbox source={card.Draft}
                    style="width:100%;box-sizing:border-box"/></label>
                  <button title={"Save card " ^ show card.Id} onclick={fn _ =>
                    title <- get card.Draft;
                    if title = "" then set message "Give the card a title."
                    else (set card.Title title; set message "")}>Save</button>
                  <p><button title={"Move card " ^ show card.Id} onclick={fn _ =>
                    stage <- get card.Stage; set card.Stage (nextStage stage)}>Move to {[stageName (nextStage target)]}</button>
                  <button title={"Delete card " ^ show card.Id} onclick={fn _ => remove card.Id}>Delete</button></p>
                </div>
              </xml>) visible;
            return <xml>
              <h2>{[stageName target]} ({[List.length visible]})</h2>
              {if List.length visible = 0 then <xml><p>No cards here.</p></xml> else <xml/>}
              {content}
            </xml>
    in
        return <xml><body>
          <h1>Task board</h1>
          <p>Add cards, edit and save their titles, and move them through the columns. Search filters as you type.</p>
          <p><label>New card: <ctextbox source={draft}/></label> <button onclick={fn _ => add ()}>Add card</button></p>
          <p><dyn signal={text <- signal message; return <xml>{[text]}</xml>}/></p>
          <p><label>Search: <ctextbox source={query}/></label> <button onclick={fn _ => set query ""}>Clear search</button></p>
          <div style="display:flex;flex-wrap:wrap;gap:16px;align-items:flex-start">
            <section style="flex:1;min-width:200px"><dyn signal={column Todo}/></section>
            <section style="flex:1;min-width:200px"><dyn signal={column Doing}/></section>
            <section style="flex:1;min-width:200px"><dyn signal={column Done}/></section>
          </div>
        </body></xml>
    end
